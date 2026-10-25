(ns rainbow.milestones.bellman-scaled-fixed-point-uniqueness
  "Held-out evidence for scaled fixed-point uniqueness of finite Bellman numerators."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness
             :as uniqueness]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path
  "artifacts/bellman-scaled-fixed-point-uniqueness/precommit.edn")
(def report-path
  "artifacts/bellman-scaled-fixed-point-uniqueness/report.edn")
(def checkpoint-path
  "artifacts/bellman-scaled-fixed-point-uniqueness/checkpoint.edn.gz")
(def default-input-checkpoint-path
  "artifacts/strict-contraction-uniqueness/checkpoint.edn.gz")

(def target-support
  [['nat/at-most-antisymmetric 'nat/at-most-antisymmetric]
   ['nat/at-most-strict-below-transitive
    'nat/at-most-strict-below-transitive]
   ['nat/positive-right-of-strict-below
    'nat/positive-right-of-strict-below]
   ['nat/multiply-right-strict-monotone-positive
    'nat/multiply-right-strict-monotone-positive]
   ['nat/recursive-max-multiply-left
    'nat/recursive-max-multiply-left]
   ['list/nat-map-max-multiply-left
    'list/nat-map-max-multiply-left]
   ['metric/finite-sup-distance-multiply-left
    'metric/finite-sup-distance-multiply-left]
   ['metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance
    'metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance]
   ['bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance
    'bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance]
   ['bellman/fixed-policy-scaled-fixed-points-unique-on-support
    'bellman/fixed-policy-scaled-fixed-points-unique-on-support]])

(def smallest-missing-prerequisite
  {'nat/at-most-antisymmetric :natural-order-antisymmetry
   'nat/at-most-strict-below-transitive :mixed-order-transitivity
   'nat/positive-right-of-strict-below :strict-upper-positivity
   'nat/multiply-right-strict-monotone-positive
   :positive-factor-strict-monotonicity
   'nat/recursive-max-multiply-left :maximum-scaling
   'list/nat-map-max-multiply-left :finite-maximum-scaling
   'metric/finite-sup-distance-multiply-left :finite-sup-scaling
   'metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance
   :scaled-fixed-point-distance-contradiction
   'bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance
   :bellman-scale-aware-contraction-instantiation
   'bellman/fixed-policy-scaled-fixed-points-unique-on-support
   :bellman-zero-distance-separation})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw
       (ex-info "Bellman scaled uniqueness precommit identity mismatch"
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

(defn- prove [checked-environment target reuse-index]
  (search/prove
   (:state
    (proof/start checked-environment (:rainbow/type target)
                 {:universes (:rainbow/universes target)}))
   (assoc preset-wide/candidate-options
          :states 32
          :depth 64
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
      (throw (ex-info "Bellman scaled uniqueness checkpoint rejected"
                      {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw
       (ex-info "Bellman scaled uniqueness input checkpoint changed"
                {:expected
                 (get-in precommit
                         [:precommit/source :input-checkpoint/id])
                 :actual (:checkpoint/id prior)})))
    (let [baseline-environment (:environment prior)
          candidate-timed
          (timed #(uniqueness/extend-environment baseline-environment))
          candidate-environment (:value candidate-timed)
          theorem-ids (uniqueness/theorem-ids candidate-environment)
          partitions
          (into {} (map (juxt :target/name :study/partition))
                (:precommit/targets precommit))
          targets
          (mapv
           (fn [[target-name support-name]]
             (let [id (get theorem-ids support-name)
                   declaration
                   (environment/declaration candidate-environment id)]
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
                                    (:value candidate-index-timed)))]
      {:precommit precommit
       :prior prior
       :environment candidate-environment
       :candidate-build-wall-ms (:wall-ms candidate-timed)
       :baseline-index-wall-ms (:wall-ms baseline-index-timed)
       :candidate-index-wall-ms (:wall-ms candidate-index-timed)
       :baseline-search-wall-ms (:wall-ms baseline-search-timed)
       :candidate-search-wall-ms (:wall-ms candidate-search-timed)
       :targets targets
       :baseline-results (:value baseline-search-timed)
       :candidate-results (:value candidate-search-timed)
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
        {:kind :finite-bellman-scaled-fixed-point-uniqueness
         :precommit/id (get-in build [:precommit :precommit/id])
         :target-names (set (map :target/name (:targets build)))
         :proof-values :native-only}
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
   :reuse-candidates (get-in result [:telemetry :reuse-candidates] 0)
   :reuse-attempts (get-in result [:telemetry :reuse-attempts] 0)
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
                 baseline
                 (compact-result (get (:baseline-results build) name))
                 candidate
                 (compact-result (get (:candidate-results build) name))]
             {:target/name name
              :study/partition (:study/partition target)
              :native/id (:native/id target)
              :baseline baseline
              :candidate candidate
              :axioms
              (kernel/axioms (:environment build) (:native/id target))
              :smallest-missing-prerequisite
              (when-not (= :proved (:status candidate))
                (get smallest-missing-prerequisite name))}))
         (:targets build))
        baseline-proved
        (filterv #(= :proved (get-in % [:baseline :status])) evaluations)
        candidate-proved
        (filterv #(= :proved (get-in % [:candidate :status])) evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-out-baseline
        (count (filter #(= :proved (get-in % [:baseline :status])) held-out))
        held-out-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) held-out))
        transfer-candidate
        (count (filter #(= :proved (get-in % [:candidate :status])) transfer))
        baseline-states
        (mapv #(get-in % [:baseline :states-created]) evaluations)
        candidate-states
        (mapv #(get-in % [:candidate :states-created]) evaluations)
        theorem-count (count (:theorem-ids build))
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        expected-targets
        (set (map :target/name
                  (get-in build [:precommit :precommit/targets])))
        passed?
        (and (= :replayed (:status replay))
             (= expected-targets (set (map :target/name evaluations)))
             (= 10 (count candidate-proved))
             (= 2 held-out-candidate)
             (= 1 transfer-candidate)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %)
                     (vals (:theorem-ids build))))
        newly-solved-held-out (- held-out-candidate held-out-baseline)
        base
        {:status (if passed? :passed :failed)
         :source
         {:precommit/id (get-in build [:precommit :precommit/id])
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :proof-values :native-only}
         :capability
         {:kind :finite-bellman-scaled-fixed-point-uniqueness
          :input-value-denominator :scale
          :bellman-output-denominator :scale-cubed
          :fixed-point-equation :bellman-value-equals-scale-squared-value
          :generalized-theorems (:theorem-ids build)
          :axiom-profiles axiom-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32
          :depth-budget 64
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
            (reduce +
                    (map #(get-in % [:baseline :wall-ms]) evaluations))}
           :candidate
           {:median-states (median candidate-states)
            :total-states (reduce + candidate-states)
            :total-search-wall-ms
            (reduce +
                    (map #(get-in % [:candidate :wall-ms]) evaluations))}}
          :timing
          {:candidate-environment-build-ms (:candidate-build-wall-ms build)
           :baseline-reuse-index-ms (:baseline-index-wall-ms build)
           :candidate-reuse-index-ms (:candidate-index-wall-ms build)
           :baseline-search-wall-ms (:baseline-search-wall-ms build)
           :candidate-search-wall-ms (:candidate-search-wall-ms build)
           :ai-latency-ms :not-instrumented}
          :lemma-leverage
          {:definition
           :newly-solved-held-out-targets-per-total-introduction-cost
           :new-generalized-theorems theorem-count
           :newly-solved-held-out-targets newly-solved-held-out
           :held-out-targets-per-new-theorem
           (/ newly-solved-held-out theorem-count)
           :all-targets-per-new-theorem
           (/ (- (count candidate-proved) (count baseline-proved))
              theorem-count)
           :measured-rainbow-introduction-ms (:candidate-build-wall-ms build)
           :ai-inclusive-cost :not-instrumented}
          :evaluations evaluations
          :remaining-failures
          (filterv #(not= :proved (get-in % [:candidate :status]))
                   evaluations)}
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
         :claim-boundaries
         {:native-targets-not-counted-as-mathlib-mappings? true
          :unscaled-raw-fixed-point-claimed? false
          :fixed-point-existence-proved? false
          :value-iteration-convergence-proved? false
          :function-equality-outside-support-claimed? false
          :trusted-kernel-change :none}}
        value-with-id (assoc base :report/id (canonical/content-id base))]
    value-with-id))

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        value (checkpoint build)
        replay (day54/replay-checkpoint value)]
    {:build build
     :checkpoint value
     :replay replay
     :report (report build value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :bellman-scaled-uniqueness/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :bellman-scaled-uniqueness/report-read-failed
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
        (when-not (= :replayed (:status result))
          (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path))]
        (write-report! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report))
          (System/exit 1))))
    (finally (shutdown-agents))))
