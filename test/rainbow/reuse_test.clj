(ns rainbow.reuse-test
  (:require [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.held-out-retrieval :as held-out-retrieval]
            [rainbow.environment :as environment]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(deftest index-and-ranking-are-deterministic-proof-data
  (let [training (held-out-retrieval/train)
        checked-environment (:environment training)
        ids (mapv #(get-in % [:declaration :rainbow/id]) (:results training))
        first-index (reuse/build-index checked-environment {:include-ids ids})
        second-index (reuse/build-index checked-environment {:include-ids ids})
        target (get-in training [:results 0 :declaration :rainbow/type])
        query (reuse/query first-index checked-environment target
                           held-out-retrieval/retrieval-policy)
        candidate (first (:candidates query))]
    (is (= first-index second-index))
    (is (= (:reuse/id first-index) (:reuse/id second-index)))
    (is (= :matched (:status query)))
    (is (= 1 (:returned query)))
    (is (= :const (first (:reuse/term candidate))))
    (is (= #{:exact-normalized-type :concept-overlap :dependency-overlap
             :successful-uses :failed-uses}
           (set (keys (:reuse/score candidate)))))
    (is (empty? (:reuse/axioms candidate)))
    (is (= :native (:reuse/source candidate)))))

(deftest build-index-quarantines-unnormalizable-types-and-indexes-the-rest
  ;; A declaration whose type cannot be normalized within the kernel reduction
  ;; budget is deterministically quarantined (telemetry) instead of aborting the
  ;; whole index; the normalizable declarations are still indexed. On a normal
  ;; environment nothing is quarantined but the telemetry field is present.
  (let [training (held-out-retrieval/train)
        checked-environment (:environment training)
        index (reuse/build-index checked-environment)]
    (is (vector? (:reuse/quarantined index)))
    (is (empty? (:reuse/quarantined index)))
    (is (seq (:reuse/entries index)))
    ;; Deterministic: two builds agree on entries and quarantine.
    (is (= (:reuse/quarantined index)
           (:reuse/quarantined (reuse/build-index checked-environment))))))

(deftest retrieval-rejects-an-environment-other-than-its-snapshot
  (let [training (held-out-retrieval/train)
        checked-environment (:environment training)
        index (reuse/build-index checked-environment)
        target (get-in training [:results 0 :declaration :rainbow/type])
        result (reuse/query index (direct-term-corpus/build-environment) target)]
    (is (= :rejected (:status result)))
    (is (= :reuse/environment-mismatch (:error/category result)))
    (is (empty? (:candidates result)))))

(deftest universe-polymorphic-retrieval-instantiates-target-levels
  (let [checked-environment (direct-term-corpus/build-environment)
        declaration-id (environment/resolve-id checked-environment
                                               'logic/polymorphic-identity)
        declaration (environment/declaration checked-environment declaration-id)
        index (reuse/build-index checked-environment)
        query (reuse/query index checked-environment
                           (:rainbow/type declaration))
        candidate (some #(when (= declaration-id
                                  (:reuse/declaration-id %)) %)
                        (:candidates query))
        result (search/prove
                (:state (proof/start checked-environment
                                     (:rainbow/type declaration)
                                     {:universes ['u]}))
                {:states 2 :reuse-index index})]
    (is (= [:const declaration-id [[:param 'u]]]
           (:reuse/term candidate)))
    (is (= :proved (:status result)))
    (is (= 1 (get-in result [:telemetry :reuse-successes])))))

(deftest exact-reuse-is-alpha-invariant-over-universe-parameter-names
  (let [checked-environment (direct-term-corpus/build-environment)
        declaration-id (environment/resolve-id checked-environment
                                               'logic/polymorphic-identity)
        declaration (environment/declaration checked-environment declaration-id)
        renamed-universe 'source_level_17
        renamed-type
        (term/instantiate-universes
         (:rainbow/type declaration)
         {'u [:param renamed-universe]})
        index (reuse/build-index checked-environment)
        query (reuse/query index checked-environment renamed-type)
        candidate (some #(when (= declaration-id
                                  (:reuse/declaration-id %)) %)
                        (:candidates query))
        result
        (search/prove
         (:state (proof/start checked-environment renamed-type
                              {:universes [renamed-universe]}))
         {:states 2 :reuse-index index})]
    (is (= [:const declaration-id [[:param renamed-universe]]]
           (:reuse/term candidate)))
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (= 1 (get-in result [:telemetry :reuse-successes])))))

(deftest related-retrieval-emits-ranked-kernel-checked-global-seeds
  (let [checked-environment (direct-term-corpus/build-environment)
        declaration-id (environment/resolve-id checked-environment
                                               'logic/polymorphic-identity)
        declaration (environment/declaration checked-environment declaration-id)
        index (reuse/build-index checked-environment)
        first-query (reuse/query-related index checked-environment
                                         (:rainbow/type declaration)
                                         {:limit 4})
        second-query (reuse/query-related index checked-environment
                                          (:rainbow/type declaration)
                                          {:limit 4})
        candidate (some #(when (= declaration-id
                                  (:reuse/declaration-id %)) %)
                        (:candidates first-query))]
    (is (= first-query second-query))
    (is (<= (:returned first-query) 4))
    (is (= [:const declaration-id [[:param 'u]]]
           (:reuse/term candidate)))
    (is (>= (get-in candidate [:reuse/score :concept-overlap]) 3))))

(deftest forged-retrieval-candidate-cannot-bypass-the-kernel
  (let [training (held-out-retrieval/train)
        checked-environment (:environment training)
        declarations (mapv :declaration (:results training))
        identity (first declarations)
        wrong (second declarations)
        index (reuse/build-index checked-environment)
        type-key (reuse/normalized-type-key checked-environment
                                            (:rainbow/type identity))
        forged (assoc-in index [:reuse/by-type type-key] [(:rainbow/id wrong)])
        started (proof/start checked-environment (:rainbow/type identity))
        result (search/prove (:state started)
                             {:states 2 :reuse-index forged})
        reuse-attempt (first (filter #(= :reuse (get-in % [:strategy :tactic]))
                                     (:attempts result)))]
    (is (= :blocked (:status result)))
    (is (= :failure (:result reuse-attempt)))
    (is (= :tactic/type-mismatch (:failure/category reuse-attempt)))
    (is (zero? (get-in result [:telemetry :reuse-successes])))))

(deftest held-out-equal-budget-ab-proves-reuse-capacity
  (let [value (held-out-retrieval/experiment)
        baseline (:baseline value)
        with-reuse (:with-reuse value)
        registrations (get-in value [:registrations :declarations])]
    (is (every? #(= :blocked (:status %)) baseline))
    (is (every? #(= :proved (:status %)) with-reuse))
    (is (= (mapv #(get-in % [:target :type]) baseline)
           (mapv #(get-in % [:target :type]) with-reuse)))
    (is (every? #(= held-out-retrieval/evaluation-budget (:evaluation/budget %))
                (concat baseline with-reuse)))
    (is (= 10 (reduce + (map #(get-in % [:telemetry :reuse-successes])
                              with-reuse))))
    (is (every? #(= :checked (get-in % [:kernel :status])) with-reuse))
    (is (= 10 (count registrations)))
    (is (every? #(empty? (:rainbow/axioms %)) registrations))
    (is (= 2 (count (:zero-use-ids value))))
    (is (empty? (get-in value [:quarantine-query :candidates])))))

(deftest recorded-report-states-scope-and-measured-delta
  (let [value (held-out-retrieval/report)]
    (is (= :passed (:status value)))
    (is (= 10 (get-in value [:benchmark :solve-rate-delta])))
    (is (= 0 (get-in value [:benchmark :baseline :proved])))
    (is (= 10 (get-in value [:benchmark :reuse :proved])))
    (is (= 10 (get-in value [:retrieval :kernel-rechecked])))
    (is (= 10 (get-in value [:retrieval :axiom-free-registrations])))
    (is (= :none (get-in value [:claim-boundaries :trusted-base-change])))
    (is (= :explicitly-quarantined
           (get-in value [:claim-boundaries :universe-polymorphic-retrieval])))))
