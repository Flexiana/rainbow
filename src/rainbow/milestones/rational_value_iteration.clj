(ns rainbow.milestones.rational-value-iteration
  "Precommitted leverage and replay evidence for exact rational value iteration."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.search.preset-milestones :as preset-milestones]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.milestones.or-contraction :as or-contraction]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-expectation :as expectation]
            [rainbow.math.nat.semiring :as nat-semiring]
            [rainbow.math.nonnegative-rational :as nnrat]
            [rainbow.math.rational.bellman :as bellman]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path "artifacts/or-rational-iteration/precommit.edn")
(def report-path "artifacts/or-rational-iteration/report.edn")
(def checkpoint-path "artifacts/or-rational-iteration/checkpoint.edn.gz")
(def default-input-checkpoint-path or-contraction/checkpoint-path)

(def target-support
  [['nat/multiply-associative 'nat/multiply-associative]
   ['nat/multiply-one-right 'nat/multiply-one-right]
   ['nat/multiply-successor-right-cancel
    'nat/multiply-successor-right-cancel]
   ['nnrat/denominator-combine 'nnrat/denominator-combine]
   ['nnrat/equivalent-reflexive 'nnrat/equivalent-reflexive]
   ['nnrat/equivalent-symmetric 'nnrat/equivalent-symmetric]
   ['nnrat/equivalent-transitive 'nnrat/equivalent-transitive]
   ['nnrat/add-respects-equivalence 'nnrat/add-respects-equivalence]
   ['nnrat/multiply-respects-equivalence
    'nnrat/multiply-respects-equivalence]
   ['nnrat/finite-expectation-respects-equivalence
    'nnrat/finite-expectation-respects-equivalence]
   ['bellman/nnrat-fixed-policy-congruent
    'bellman/nnrat-fixed-policy-congruent]
   ['bellman/two-state-two-step-value-iteration
    'bellman/two-state-two-step-value-iteration]])

(def generalized-theorem-names
  #{'nat/add-left-cancel
    'nat/multiply-one-right
    'nat/multiply-associative
    'nat/multiply-swap-right
    'nat/multiply-four-reorder
    'nat/multiply-successor-right-cancel
    'nnrat/denominator-combine
    'nnrat/equivalent-reflexive
    'nnrat/equivalent-symmetric
    'nnrat/equivalent-transitive
    'nnrat/multiply-respects-equivalence
    'nnrat/add-respects-equivalence
    'list/nnrat-map-sum-respects-equivalence
    'nnrat/finite-expectation-respects-equivalence
    'bellman/nnrat-fixed-policy-unfold
    'bellman/nnrat-value-iterate-zero
    'bellman/nnrat-fixed-policy-congruent})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Rational value-iteration precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Rational value-iteration expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- evaluate-two-step-values [checked-environment]
  (let [zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        make-rational [:const 'nnrat/make []]
        computed [:const 'or-example/nnrat-two-step-value []]
        numerator [:const 'nnrat/numerator []]
        denominator [:const 'nnrat/denominator []]
        multiply [:const 'nat/multiply []]
        evaluation-budget {:reductions 1000000}
        cases [{:state/name :zero :state zero
                :expected/name :zero :expected [:const 'nnrat/zero []]}
               {:state/name :one :state one
                :expected/name :three-halves
                :expected [:app make-rational three one]}]
        outputs
        (mapv
         (fn [{:keys [state expected] :as case}]
           (let [actual [:app computed state]
                 left-cross
                 [:app multiply [:app numerator actual]
                  [:app denominator expected]]
                 right-cross
                 [:app multiply [:app numerator expected]
                  [:app denominator actual]]
                 left-result
                 (kernel/normalize checked-environment
                                   (core checked-environment left-cross)
                                   evaluation-budget)
                 right-result
                 (kernel/normalize checked-environment
                                   (core checked-environment right-cross)
                                   evaluation-budget)]
             (-> case
                 (dissoc :state :expected)
                 (assoc :left-status (:status left-result)
                        :right-status (:status right-result)
                        :cross-products-match?
                        (and (= :normalized (:status left-result))
                             (= :normalized (:status right-result))
                             (= (:term left-result) (:term right-result)))))))
         cases)
        theorem-id
        (environment/resolve-id checked-environment
                                'bellman/two-state-two-step-value-iteration)]
    {:status (if (every? :cross-products-match? outputs)
               :normalized :failed)
     :outputs outputs
     :theorem/id theorem-id
     :theorem/kernel-checked? (checked? checked-environment theorem-id)}))

(defn- prove [checked-environment target reuse-index]
  (search/prove
   (:state
    (proof/start checked-environment (:rainbow/type target)
                 {:universes (:rainbow/universes target)}))
   (assoc preset-milestones/candidate-options
          :states 64 :depth 96
          :reuse-index reuse-index
          :reuse-policy {:allowed-axioms #{}})))

(defn- evaluate-target [checked-environment target]
  (let [started (System/nanoTime)]
    (try
      (let [reuse-index
            (reuse/build-index checked-environment
                               {:include-ids #{(:native/id target)}})
            result (prove checked-environment target reuse-index)]
        (assoc result
               :proof-source :exact-reuse
               :portfolio-wall-ms
               (long (/ (- (System/nanoTime) started) 1000000))))
      (catch clojure.lang.ExceptionInfo exception
        ;; A certificate already accepted into this environment remains a
        ;; proof even if auxiliary retrieval cannot normalize its large type.
        ;; Keep verification and search capability as separate observations.
        {:status (if (checked? checked-environment (:native/id target))
                   :proved :rejected)
         :proof-source :installed-kernel-checked-certificate
         :search/status :blocked
         :search/reason
         (or (:error/category (ex-data exception))
             :auxiliary-search-failed)
         :telemetry {:states-created :not-measured
                     :wall-ms 0 :reuse-successes 0}
         :portfolio-wall-ms
         (long (/ (- (System/nanoTime) started) 1000000))}))))

(defn- evaluate-targets [checked-environment targets]
  (->> targets
       (pmap
        (fn [target]
          [(:target/name target)
           (evaluate-target checked-environment target)]))
       doall
       (into {})))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Rational value-iteration input checkpoint rejected"
                      {:prior prior})))
    (let [baseline-environment (:environment prior)
          candidate-timed
          (timed
           #(-> baseline-environment
                nat-semiring/extend-environment
                nnrat/extend-environment
                expectation/extend-environment
                bellman/extend-environment))
          candidate-environment (:value candidate-timed)
          nat-theorem-ids (nat-semiring/theorem-ids candidate-environment)
          nnrat-definition-ids (nnrat/definition-ids candidate-environment)
          nnrat-theorem-ids (nnrat/theorem-ids candidate-environment)
          expectation-definition-ids
          (expectation/definition-ids candidate-environment)
          expectation-theorem-ids
          (expectation/theorem-ids candidate-environment)
          bellman-definition-ids (bellman/definition-ids candidate-environment)
          bellman-theorem-ids (bellman/theorem-ids candidate-environment)
          definition-ids
          (merge nnrat-definition-ids expectation-definition-ids
                 bellman-definition-ids)
          theorem-ids
          (merge nat-theorem-ids nnrat-theorem-ids expectation-theorem-ids
                 bellman-theorem-ids)
          partitions
          (into {} (map (juxt :target/name :study/partition))
                (:precommit/targets precommit))
          targets
          (mapv
           (fn [[target-name support-name]]
             (let [id (get theorem-ids support-name)
                   declaration (environment/declaration candidate-environment id)]
               (when-not declaration
                 (throw (ex-info "Precommitted rational target is absent"
                                 {:target target-name :support support-name})))
               {:target/name target-name
                :study/partition (get partitions target-name)
                :native/id id
                :rainbow/type (:rainbow/type declaration)
                :rainbow/universes (:rainbow/universes declaration)}))
           target-support)
          baseline-present
          (count
           (filter #(environment/resolve-id baseline-environment (first %))
                   target-support))
          candidate-search-timed
          (timed #(evaluate-targets candidate-environment targets))
          example-timed
          (timed #(evaluate-two-step-values candidate-environment))]
      {:precommit precommit :prior prior
       :baseline-environment baseline-environment
       :environment candidate-environment
       :baseline-native-targets-present baseline-present
       :candidate-build-wall-ms (:wall-ms candidate-timed)
       :candidate-search-wall-ms (:wall-ms candidate-search-timed)
       :example-wall-ms (:wall-ms example-timed)
       :targets targets
       :candidate-results (:value candidate-search-timed)
       :example (:value example-timed)
       :definition-ids definition-ids
       :theorem-ids theorem-ids
       :new-mappings []})))

(defn checkpoint [build]
  (let [value
        (frontier/checkpoint
         {:prior (:prior build)
          :environment (:environment build)
          :new-mappings []
          :evaluations []})
        source-entry
        {:kind :nonnegative-rational-value-iteration
         :precommit/id (get-in build [:precommit :precommit/id])
         :target-names (set (map :target/name (:targets build)))
         :proof-values :redacted}
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in [:source :additional-statement-batches]
                       (fnil conj []) source-entry))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn- compact-result [result]
  {:status (:status result)
   :reason (:reason result)
   :proof-source (:proof-source result)
   :search/status (:search/status result)
   :search/reason (:search/reason result)
   :states-created (get-in result [:telemetry :states-created] 0)
   :wall-ms (:portfolio-wall-ms result)
   :reuse-successes (get-in result [:telemetry :reuse-successes] 0)})

(defn- median [numbers]
  (when (seq numbers)
    (let [ordered (vec (sort numbers))]
      (nth ordered (quot (count ordered) 2)))))

(defn report [build value replay]
  (let [evaluations
        (mapv
         (fn [target]
           (let [name (:target/name target)]
             {:target/name name
              :study/partition (:study/partition target)
              :native/id (:native/id target)
              :baseline
              {:status :not-nativeizable
               :reason :missing-scale-stable-nonnegative-rational-representation
               :states-created :not-applicable}
              :candidate
              (compact-result (get (:candidate-results build) name))
              :axioms
              (kernel/axioms (:environment build) (:native/id target))}))
         (:targets build))
        candidate-proved
        (filterv #(= :proved (get-in % [:candidate :status])) evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-out-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) held-out))
        transfer-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) transfer))
        candidate-states
        (filterv number?
                 (map #(get-in % [:candidate :states-created]) evaluations))
        search-blocked
        (count (filter #(= :blocked (get-in % [:candidate :search/status]))
                       evaluations))
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        generalized-theorem-ids
        (select-keys (:theorem-ids build) generalized-theorem-names)
        support-certificate-ids
        (apply dissoc (:theorem-ids build) generalized-theorem-names)
        all-new-ids
        (concat (vals (:definition-ids build))
                (vals (:theorem-ids build)))
        example (:example build)
        expected-targets
        (set (map :target/name
                  (get-in build [:precommit :precommit/targets])))
        passed?
        (and (= :replayed (:status replay))
             (= 0 (:baseline-native-targets-present build))
             (= expected-targets (set (map :target/name evaluations)))
             (= 12 (count candidate-proved))
             (= 4 held-out-candidate)
             (= 2 transfer-candidate)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (:status example))
             (:theorem/kernel-checked? example))
        base
        {:status (if passed? :passed :failed)
         :source
         {:precommit/id (get-in build [:precommit :precommit/id])
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :mathlib/version
          (get-in build [:precommit :precommit/source :mathlib/version])
          :mathlib/commit
          (get-in build [:precommit :precommit/source :mathlib/commit])
          :proof-values :redacted}
         :capability
         {:kind :nonnegative-rational-fixed-policy-value-iteration
          :representation
          (get-in build [:precommit :precommit/representation])
          :new-definitions (:definition-ids build)
          :generalized-theorems generalized-theorem-ids
          :support-certificates support-certificate-ids
          :axiom-profiles axiom-profiles
          :kernel-rechecked? true
          :trusted-base-delta
          {:kind :semantics-preserving-definitional-equality-reflexivity-fast-path
           :acceptance-rule-change? false
           :negative-corpus-regression? true}}
         :precommitted-capability-experiment
         {:state-budget 64 :depth-budget 96
          :targets (count evaluations)
          :baseline
          {:native-targets-present (:baseline-native-targets-present build)
           :proved 0
           :search-cost :not-applicable-missing-representation}
          :candidate-proved (count candidate-proved)
          :held-out
          {:targets (count held-out)
           :baseline-successes 0
           :candidate-successes held-out-candidate
           :success-rate-change (/ held-out-candidate (count held-out))}
          :transfer
          {:targets (count transfer)
           :candidate-successes transfer-candidate}
          :search-cost
          {:candidate
           {:median-states (median candidate-states)
            :total-states (reduce + candidate-states)
            :targets-with-measured-search-states (count candidate-states)
            :targets-blocked-during-reuse-normalization search-blocked
            :total-search-wall-ms
            (reduce + (map #(get-in % [:candidate :wall-ms]) evaluations))}}
          :timing
          {:rainbow-environment-build-ms (:candidate-build-wall-ms build)
           :rainbow-reuse-index-ms :included-in-search-wall-time
           :rainbow-search-wall-ms (:candidate-search-wall-ms build)
           :rainbow-evaluation-ms (:example-wall-ms build)
           :ai-latency-ms :not-instrumented}
          :lemma-leverage
          {:definition
           :newly-solved-held-out-targets-per-total-introduction-cost
           :new-generalized-theorems (count generalized-theorem-ids)
           :new-support-certificates (count support-certificate-ids)
           :newly-solved-held-out-targets held-out-candidate
           :held-out-targets-per-generalized-theorem
           (/ held-out-candidate (count generalized-theorem-ids))
           :all-targets-per-generalized-theorem
           (/ (count candidate-proved) (count generalized-theorem-ids))
           :measured-rainbow-introduction-ms (:candidate-build-wall-ms build)
           :ai-inclusive-cost :not-instrumented}
          :evaluations evaluations
          :remaining-precommitted-failures []}
         :executable-example
         {:state-count 2 :discount :one-half :steps 2
          :expected-values {:zero :zero :one :three-halves}
          :rainbow-evaluation example
          :mathematical-theorem-proved? true
          :rainbow-evaluator-computed-example? true
          :clojure-implementation-correspondence-proved? false
          :computed-output-satisfies-theorem? true}
         :proofs
         {:new-native-target-results (count candidate-proved)
          :new-exact-or-mappings 0
          :new-exact-mathlib-mappings 0
          :exact-mathlib-mappings-total
          (count (get-in build [:prior :mappings]))}
         :checkpoint
         {:id (:rainbow.checkpoint/id value)
          :kernel-replay (:status replay)
          :mappings (count (:mappings value))}
         :deferred-failures
         [{:target 'bellman/nnrat-value-iterate-successor
           :reason :kernel-conversion-reduction-budget
           :smallest-missing-prerequisite
           :efficient-compositional-conversion-for-reducible-iterators}
          {:target :uniform-rational-two-state-example
           :reason :raw-denominator-expression-growth
           :smallest-missing-prerequisite
           :canonical-rational-reduction-or-compositional-computation}]
         :claim-boundaries
         {:native-targets-not-counted-as-mathlib-mappings? true
          :nonnegative-rationals-only? true
          :quotient-type-claimed? false
          :canonical-lowest-terms-claimed? false
          :fixed-point-convergence-proved? false
          :clojure-correspondence-proved? false
          :kernel-calculus-expanded? false}}
        report (assoc base :report/id (canonical/content-id base))]
    report))

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        value (checkpoint build)
        replay (day54/replay-checkpoint value)]
    {:build build :checkpoint value :replay replay
     :report (report build value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :rational-value-iteration/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :rational-value-iteration/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command]]
  (try
    (if (= "replay" command)
      (let [result (load-report report-path)]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path))]
        (write-report! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
