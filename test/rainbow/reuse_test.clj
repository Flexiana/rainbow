(ns rainbow.reuse-test
  (:require [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.held-out-retrieval :as held-out-retrieval]
            [rainbow.data.inductive :as inductive]
            [rainbow.elaborate :as elaborate]
            [rainbow.math.logic.function :as f]
            [rainbow.math.logic.proposition :as proposition]
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

(deftest incremental-index-retains-the-entire-legacy-index-and-id
  (let [env (direct-term-corpus/build-environment)
        id (environment/resolve-id env 'logic/polymorphic-identity)]
    (doseq [options [{} {:include-ids [id]}
                     {:lifecycle {id :quarantined}
                      :evidence {id {:successful-uses 7 :failed-uses 3}}}]]
      (is (= (reuse/build-index env options)
             (reuse/build-index env (assoc options :incremental? true)))))))

(deftest normalized-literal-types-have-no-universe-parameters
  (let [env (inductive/build-environment)
        type (:term (elaborate/core-expression env
                     (f/equality [:succ [:zero]] (f/const* 'data/Nat []) [:nat 2] [:nat 2])))]
    (is type)
    (is (= (reuse/normalized-type-key env type)
           (reuse/normalized-type-key env type nil {:incremental? true})))))

(deftest shared-universe-renaming-preserves-the-legacy-term
  (let [leaf [:const "sha256:example" [[:max [:param 'v] [:zero]] [:param 'u]]]
        shared (nth (iterate #(term/application % %) leaf) 10)]
    (doseq [parameters [[] ['u] ['v 'u]]]
      (is (= (#'reuse/canonicalize-universe-parameters shared parameters)
             (#'reuse/canonicalize-universe-dag shared parameters))))))

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

(deftest native-logic-steps-take-lemmas-through-the-index-policy-and-hold-out
  ;; B and A from A and B: the native conjunction steps use proposition/left, right and
  ;; conjoin. They used to take them from the environment past the index; now a lemma held
  ;; out of the index (or outside its policy) is not used, as for an indexed lemma.
  (let [environment (proposition/build-environment)
        target (:term (elaborate/core-expression
                       environment
                       (proposition/forall [['A 'Prop] ['B 'Prop] ['evidence (proposition/conjunction 'A 'B)]]
                                           (proposition/conjunction 'B 'A))))
        index (reuse/build-index environment {:incremental? true})
        options {:states 256 :depth 32 :wall-ms 5000 :native-logic-focus? true :native-logic-prune? true}
        search #(search/prove (:state (proof/start environment target)) (merge options %))
        lemmas (fn [result] (set (filter #(= :theorem (:rainbow/kind (environment/declaration environment %)))
                                         (term/constants (get-in result [:proof :proof/term])))))
        full (search {:reuse-index index})
        used (lemmas full)
        held-out (fn [ids] (-> index
                               (update :reuse/entries #(filterv (comp not ids :reuse/declaration-id) %))
                               (update :reuse/by-type #(into (sorted-map) (keep (fn [[k v]] (let [v (filterv (comp not ids) v)] (when (seq v) [k v])))) %))))
        without (search {:reuse-index (held-out used)})
        denied (search {:reuse-index index :reuse-policy {:denied-dependencies (set (mapcat #(:rainbow/dependencies (environment/declaration environment %)) used))}})]
    (is (= :proved (:status full)))
    (is (= 3 (count used)))
    (is (= :proved (:status (search {}))) "without an index the native steps are unchanged")
    (is (empty? (some-> (get-in without [:proof :proof/term]) term/constants (filter used))))
    (is (= :blocked (:status without)))
    (is (not= :proved (:status denied)))
    (is (true? ((reuse/admits index environment {} nil) [(term/constant (first used) [])])))
    (is (false? ((reuse/admits (held-out used) environment {} nil) [[:hole "g-1"] (term/constant (first used) [])])))
    (is (true? ((reuse/admits (held-out used) environment {} [:app (term/constant (first used) []) [:hole "g-0"]])
                [(term/constant (first used) [])])) "a proposal's own lemmas pass")))
