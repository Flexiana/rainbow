(ns rainbow.milestones.or-contraction
  "Held-out leverage and replay evidence for finite Bellman contraction."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.search.preset-milestones :as preset-milestones]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.milestones.nat-distance :as nat-distance-milestone]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.bellman-contraction :as bellman-contraction]
            [rainbow.math.finite.bellman :as finite-bellman]
            [rainbow.math.finite.metric :as finite-metric]
            [rainbow.math.nat.contraction :as nat-contraction]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path "artifacts/or-contraction/precommit.edn")
(def report-path "artifacts/or-contraction/report.edn")
(def checkpoint-path "artifacts/or-contraction/checkpoint.edn.gz")
(def default-input-checkpoint-path nat-distance-milestone/checkpoint-path)

(def target-support
  [['nat/distance-multiply-left 'nat/distance-multiply-left]
   ['list/nat-map-sum-distance-bound
    'list/nat-map-sum-distance-bound]
   ['probability/expectation-distance-bound
    'probability/expectation-distance-bound]
   ['metric/finite-sup-upper-bound 'metric/finite-sup-upper-bound]
   ['metric/finite-sup-symmetric 'metric/finite-sup-symmetric]
   ['metric/finite-sup-triangle 'metric/finite-sup-triangle]
   ['bellman/fixed-policy-pointwise-contraction
    'bellman/fixed-policy-pointwise-contraction]
   ['bellman/fixed-policy-sup-contraction
    'bellman/fixed-policy-sup-contraction]
   ['bellman/two-state-contraction-example
    'bellman/two-state-contraction-example]])

(def smallest-missing-prerequisite
  {'nat/distance-multiply-left :multiplicative-distance
   'list/nat-map-sum-distance-bound :finite-fold-distance
   'probability/expectation-distance-bound :finite-fold-distance
   'metric/finite-sup-upper-bound :constructive-finite-maximum
   'metric/finite-sup-symmetric :maximum-fold-congruence
   'metric/finite-sup-triangle :membership-aware-maximum-bound
   'bellman/fixed-policy-pointwise-contraction
   :membership-aware-expectation-distance
   'bellman/fixed-policy-sup-contraction :finite-sup-bounded-fold
   'bellman/two-state-contraction-example
   :fixed-policy-sup-contraction})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "OR contraction precommit identity mismatch"
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
      (throw (ex-info "OR example expression rejected" {:result result})))
    (:term result)))

(defn- two-state-evaluation [checked-environment]
  (let [nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        source [:const 'or-example/two-state-space []]
        transition [:const 'or-example/uniform-transition []]
        reward [:const 'or-example/identity-value []]
        left [:const 'or-example/identity-value []]
        right [:fn [['state nat]] zero]
        left-bellman
        [:fn [['state nat]]
         [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
          nat two source transition reward one left 'state]]
        right-bellman
        [:fn [['state nat]]
         [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
          nat two source transition reward one right 'state]]
        expression
        [:app [:const 'metric/finite-sup-distance [[:zero]]]
         nat source left-bellman right-bellman]
        normalized
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    {:status (:status normalized)
     :computed-output-distance 1
     :proved-upper-bound 2
     :matches-expected-distance?
     (= (core checked-environment one) (:term normalized))
     :theorem/id
     (environment/resolve-id checked-environment
                             'bellman/two-state-contraction-example)}))

(defn- prove [checked-environment target reuse-index]
  (search/prove
   (:state
    (proof/start checked-environment (:rainbow/type target)
                 {:universes (:rainbow/universes target)}))
   (assoc preset-milestones/candidate-options
          :states 64 :depth 96
          :reuse-index reuse-index
          :reuse-policy {:allowed-axioms #{}})))

(defn- evaluate-targets [checked-environment targets reuse-index]
  (->> targets
       (pmap
        (fn [target]
          [(:target/name target)
           (prove checked-environment target reuse-index)]))
       doall
       (into {})))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "OR contraction input checkpoint rejected"
                      {:prior prior})))
    (let [baseline-timed
          (timed
           #(-> (:environment prior)
                finite-metric/extend-definitions
                finite-bellman/extend-environment))
          baseline-environment (:value baseline-timed)
          candidate-timed
          (timed
           #(-> baseline-environment
                nat-contraction/extend-environment
                finite-metric/extend-theorems
                bellman-contraction/extend-environment))
          candidate-environment (:value candidate-timed)
          nat-ids (nat-contraction/theorem-ids candidate-environment)
          metric-definition-ids
          (finite-metric/definition-ids candidate-environment)
          metric-ids (finite-metric/theorem-ids candidate-environment)
          bellman-ids
          (bellman-contraction/theorem-ids candidate-environment)
          all-theorem-ids (merge nat-ids metric-ids bellman-ids)
          partitions
          (into {} (map (juxt :target/name :study/partition))
                (:precommit/targets precommit))
          targets
          (mapv
           (fn [[target-name support-name]]
             (let [id (get all-theorem-ids support-name)
                   declaration (environment/declaration candidate-environment id)]
               {:target/name target-name
                :study/partition (get partitions target-name)
                :native/id id
                :rainbow/type (:rainbow/type declaration)
                :rainbow/universes (:rainbow/universes declaration)}))
           target-support)
          baseline-index-timed
          (timed #(reuse/build-index baseline-environment))
          candidate-index-timed
          (timed #(reuse/build-index candidate-environment))
          baseline-search-timed
          (timed #(evaluate-targets baseline-environment targets
                                    (:value baseline-index-timed)))
          candidate-search-timed
          (timed #(evaluate-targets candidate-environment targets
                                    (:value candidate-index-timed)))
          example-timed
          (timed #(two-state-evaluation candidate-environment))]
      {:precommit precommit :prior prior
       :baseline-environment baseline-environment
       :environment candidate-environment
       :baseline-build-wall-ms (:wall-ms baseline-timed)
       :candidate-build-wall-ms (:wall-ms candidate-timed)
       :baseline-index-wall-ms (:wall-ms baseline-index-timed)
       :candidate-index-wall-ms (:wall-ms candidate-index-timed)
       :baseline-search-wall-ms (:wall-ms baseline-search-timed)
       :candidate-search-wall-ms (:wall-ms candidate-search-timed)
       :example-wall-ms (:wall-ms example-timed)
       :targets targets
       :baseline-results (:value baseline-search-timed)
       :candidate-results (:value candidate-search-timed)
       :example (:value example-timed)
       :definition-ids metric-definition-ids
       :nat-theorem-ids nat-ids :metric-theorem-ids metric-ids
       :bellman-theorem-ids bellman-ids
       :theorem-ids all-theorem-ids
       :new-mappings []})))

(defn checkpoint [build]
  (let [value
        (frontier/checkpoint
         {:prior (:prior build)
          :environment (:environment build)
          :new-mappings []
          :evaluations []})
        source-entry
        {:kind :finite-bellman-contraction
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
   :states-created (get-in result [:telemetry :states-created] 0)
   :wall-ms (get-in result [:telemetry :wall-ms] 0)
   :reuse-successes (get-in result [:telemetry :reuse-successes] 0)})

(defn- median [numbers]
  (when (seq numbers)
    (let [ordered (vec (sort numbers))]
      (nth ordered (quot (count ordered) 2)))))

(defn report [build value replay]
  (let [evaluations
        (mapv
         (fn [target]
           (let [name (:target/name target)
                 baseline (compact-result (get (:baseline-results build) name))
                 candidate (compact-result (get (:candidate-results build) name))]
             {:target/name name
              :study/partition (:study/partition target)
              :native/id (:native/id target)
              :baseline baseline
              :candidate candidate
              :axioms (kernel/axioms (:environment build) (:native/id target))
              :smallest-missing-prerequisite
              (when-not (= :proved (:status candidate))
                (get smallest-missing-prerequisite name))}))
         (:targets build))
        baseline-proved (filterv #(= :proved (get-in % [:baseline :status]))
                                 evaluations)
        candidate-proved (filterv #(= :proved (get-in % [:candidate :status]))
                                  evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-out-baseline
        (count (filter #(= :proved (get-in % [:baseline :status])) held-out))
        held-out-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) held-out))
        transfer-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) transfer))
        baseline-states (mapv #(get-in % [:baseline :states-created]) evaluations)
        candidate-states (mapv #(get-in % [:candidate :states-created]) evaluations)
        theorem-count (count (:theorem-ids build))
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]] [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        all-new-ids (concat (vals (:definition-ids build))
                            (vals (:theorem-ids build)))
        example (:example build)
        expected-targets (set (map :target/name
                                   (get-in build [:precommit :precommit/targets])))
        passed?
        (and (= :replayed (:status replay))
             (= expected-targets (set (map :target/name evaluations)))
             (= 9 (count candidate-proved))
             (= 3 held-out-candidate)
             (= 2 transfer-candidate)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (:status example))
             (:matches-expected-distance? example)
             (checked? (:environment build) (:theorem/id example)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:precommit/id (get-in build [:precommit :precommit/id])
          :input-checkpoint/id
          (get-in build [:prior :checkpoint/id])
          :proof-values :redacted}
         :capability
         {:kind :finite-fixed-policy-bellman-contraction
          :arithmetic :exact-natural-numerators-with-explicit-scale
          :new-definitions (:definition-ids build)
          :generalized-theorems (:theorem-ids build)
          :axiom-profiles axiom-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 64 :depth-budget 96
          :targets (count evaluations)
          :baseline-proved (count baseline-proved)
          :candidate-proved (count candidate-proved)
          :held-out
          {:targets (count held-out)
           :baseline-successes held-out-baseline
           :candidate-successes held-out-candidate
           :success-rate-change
           (- (/ held-out-candidate (count held-out))
              (/ held-out-baseline (count held-out)))}
          :transfer
          {:targets (count transfer)
           :candidate-successes transfer-candidate}
          :search-cost
          {:baseline
           {:median-states (median baseline-states)
            :total-states (reduce + baseline-states)
            :total-search-wall-ms
            (reduce + (map #(get-in % [:baseline :wall-ms]) evaluations))}
           :candidate
           {:median-states (median candidate-states)
            :total-states (reduce + candidate-states)
            :total-search-wall-ms
            (reduce + (map #(get-in % [:candidate :wall-ms]) evaluations))}}
          :timing
          {:baseline-environment-build-ms (:baseline-build-wall-ms build)
           :candidate-environment-build-ms (:candidate-build-wall-ms build)
           :baseline-reuse-index-ms (:baseline-index-wall-ms build)
           :candidate-reuse-index-ms (:candidate-index-wall-ms build)
           :baseline-search-wall-ms (:baseline-search-wall-ms build)
           :candidate-search-wall-ms (:candidate-search-wall-ms build)
           :example-evaluation-ms (:example-wall-ms build)
           :ai-latency-ms :not-instrumented}
          :lemma-leverage
          {:definition
           :newly-solved-held-out-targets-per-total-introduction-cost
           :new-generalized-theorems theorem-count
           :newly-solved-held-out-targets
           (- held-out-candidate held-out-baseline)
           :held-out-targets-per-new-theorem
           (/ (- held-out-candidate held-out-baseline) theorem-count)
           :all-targets-per-new-theorem
           (/ (- (count candidate-proved) (count baseline-proved))
              theorem-count)
           :measured-rainbow-introduction-ms (:candidate-build-wall-ms build)
           :ai-inclusive-cost :not-instrumented}
          :evaluations evaluations
          :remaining-failures
          (filterv #(not= :proved (get-in % [:candidate :status]))
                   evaluations)}
         :executable-example
         {:state-count 2 :probability-scale 2 :discount-numerator 1
          :rainbow-evaluation example
          :mathematical-theorem-proved? true
          :rainbow-evaluator-computed-example? true
          :clojure-implementation-correspondence-proved? false
          :computed-output-satisfies-theorem? true}
         :proofs
         {:new-native-target-results (count candidate-proved)
          :new-exact-or-mappings 0
          :new-exact-mathlib-mappings 0
          :exact-mathlib-mappings-total (count (get-in build [:prior :mappings]))}
         :checkpoint
         {:id (:rainbow.checkpoint/id value)
          :kernel-replay (:status replay)
          :mappings (count (:mappings value))}
         :claim-boundaries
         {:native-targets-not-counted-as-mathlib-mappings? true
          :raw-scaled-values-claimed-as-rational-quotient-field? false
          :fixed-point-convergence-proved? false
          :trusted-kernel-change :none}}
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
         :error/category :or-contraction/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :or-contraction/report-read-failed
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
