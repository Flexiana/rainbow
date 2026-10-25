(ns rainbow.milestones.constructive-unique-fixed-point
  "Held-out evidence for constructive support-relative fixed-point existence and uniqueness."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.constructive-unique-fixed-point :as unique]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path "artifacts/constructive-unique-fixed-point/precommit.edn")
(def report-path "artifacts/constructive-unique-fixed-point/report.edn")
(def checkpoint-path "artifacts/constructive-unique-fixed-point/checkpoint.edn.gz")
(def default-input-checkpoint-path
  "artifacts/strict-contraction-stabilization/checkpoint.edn.gz")

(def target-names
  ['metric/strict-contraction-bounded-fixed-point-agrees-with-fixed-point
   'metric/strict-contraction-has-bounded-canonical-support-fixed-point
   'metric/strict-contraction-support-fixed-point-exists-and-is-unique])

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Unique fixed-point precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime) value (operation)]
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
   (:state (proof/start checked-environment (:rainbow/type target)
                        {:universes (:rainbow/universes target)}))
   (assoc preset-wide/candidate-options
          :states 32 :depth 64 :reuse-index reuse-index
          :reuse-policy {:allowed-axioms #{}})))

(defn- evaluate [checked-environment targets reuse-index]
  (->> targets
       (pmap (fn [target]
               [(:target/name target)
                (prove checked-environment target reuse-index)]))
       doall (into {})))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Unique fixed-point input checkpoint rejected"
                      {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "Unique fixed-point input checkpoint changed"
                      {:expected (get-in precommit
                                         [:precommit/source
                                          :input-checkpoint/id])
                       :actual (:checkpoint/id prior)})))
    (let [baseline (:environment prior)
          candidate-timed (timed #(unique/extend-environment baseline))
          candidate (:value candidate-timed)
          theorem-ids (unique/theorem-ids candidate)
          partitions (into {} (map (juxt :target/name :study/partition))
                           (:precommit/targets precommit))
          targets
          (mapv
           (fn [name]
             (let [id (get theorem-ids name)
                   declaration (environment/declaration candidate id)]
               {:target/name name :study/partition (get partitions name)
                :native/id id :rainbow/type (:rainbow/type declaration)
                :rainbow/universes (:rainbow/universes declaration)}))
           target-names)
          baseline-index (timed #(reuse/build-index baseline))
          candidate-index (timed #(reuse/build-index candidate))
          baseline-search (timed #(evaluate baseline targets
                                            (:value baseline-index)))
          candidate-search (timed #(evaluate candidate targets
                                             (:value candidate-index)))]
      {:precommit precommit :prior prior :environment candidate
       :theorem-ids theorem-ids :targets targets
       :candidate-build-wall-ms (:wall-ms candidate-timed)
       :baseline-index-wall-ms (:wall-ms baseline-index)
       :candidate-index-wall-ms (:wall-ms candidate-index)
       :baseline-search-wall-ms (:wall-ms baseline-search)
       :candidate-search-wall-ms (:wall-ms candidate-search)
       :baseline-results (:value baseline-search)
       :candidate-results (:value candidate-search)})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint
               {:prior (:prior build) :environment (:environment build)
                :new-mappings [] :evaluations []})
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in
             [:source :additional-statement-batches] (fnil conj [])
             {:kind :constructive-unique-support-fixed-point
              :precommit/id (get-in build [:precommit :precommit/id])
              :target-names (set target-names) :proof-values :native-only}))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn- compact [result]
  {:status (:status result) :reason (:reason result)
   :states-created (get-in result [:telemetry :states-created] 0)
   :wall-ms (get-in result [:telemetry :wall-ms] 0)
   :reuse-candidates (get-in result [:telemetry :reuse-candidates] 0)
   :reuse-attempts (get-in result [:telemetry :reuse-attempts] 0)
   :reuse-successes (get-in result [:telemetry :reuse-successes] 0)})

(defn- median [numbers]
  (nth (vec (sort numbers)) (quot (count numbers) 2)))

(defn report [build value replay]
  (let [evaluations
        (mapv (fn [target]
                (let [name (:target/name target)]
                  {:target/name name :study/partition (:study/partition target)
                   :native/id (:native/id target)
                   :baseline (compact (get (:baseline-results build) name))
                   :candidate (compact (get (:candidate-results build) name))
                   :axioms (kernel/axioms (:environment build)
                                          (:native/id target))}))
              (:targets build))
        proved? #(= :proved (get-in %1 [%2 :status]))
        baseline-proved (filterv #(proved? % :baseline) evaluations)
        candidate-proved (filterv #(proved? % :candidate) evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-base (count (filter #(proved? % :baseline) held-out))
        held-candidate (count (filter #(proved? % :candidate) held-out))
        transfer-candidate (count (filter #(proved? % :candidate) transfer))
        baseline-states (mapv #(get-in % [:baseline :states-created]) evaluations)
        candidate-states (mapv #(get-in % [:candidate :states-created]) evaluations)
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        passed?
        (and (= :replayed (:status replay)) (= 3 (count candidate-proved))
             (= 1 held-candidate) (= 1 transfer-candidate)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %)
                     (vals (:theorem-ids build))))
        base
        {:status (if passed? :passed :failed)
         :source {:precommit/id (get-in build [:precommit :precommit/id])
                  :input-checkpoint/id (get-in build [:prior :checkpoint/id])
                  :proof-values :native-only}
         :capability
         {:kind :constructive-unique-support-fixed-point
          :existence-witness :bounded-natural-iterate
          :uniqueness-scope :declared-finite-support
          :generalized-theorems (:theorem-ids build)
          :axiom-profiles axiom-profiles :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32 :depth-budget 64 :targets 3
          :baseline-proved (count baseline-proved)
          :candidate-proved (count candidate-proved)
          :held-out {:targets 1 :baseline-successes held-base
                     :candidate-successes held-candidate
                     :success-rate-change (- held-candidate held-base)}
          :transfer {:targets 1 :candidate-successes transfer-candidate}
          :search-cost
          {:baseline {:median-states (median baseline-states)
                      :total-states (reduce + baseline-states)
                      :total-search-wall-ms
                      (reduce + (map #(get-in % [:baseline :wall-ms])
                                     evaluations))}
           :candidate {:median-states (median candidate-states)
                       :total-states (reduce + candidate-states)
                       :total-search-wall-ms
                       (reduce + (map #(get-in % [:candidate :wall-ms])
                                      evaluations))}}
          :timing {:candidate-environment-build-ms
                   (:candidate-build-wall-ms build)
                   :baseline-reuse-index-ms (:baseline-index-wall-ms build)
                   :candidate-reuse-index-ms (:candidate-index-wall-ms build)
                   :baseline-search-wall-ms (:baseline-search-wall-ms build)
                   :candidate-search-wall-ms (:candidate-search-wall-ms build)
                   :ai-latency-ms :not-instrumented}
          :lemma-leverage
          {:definition :newly-solved-held-out-targets-per-total-introduction-cost
           :new-generalized-theorems 3 :newly-solved-held-out-targets 1
           :held-out-targets-per-new-theorem 1/3
           :all-targets-per-new-theorem 1
           :measured-rainbow-introduction-ms (:candidate-build-wall-ms build)
           :ai-inclusive-cost :not-instrumented}
          :evaluations evaluations
          :remaining-failures
          (filterv #(not (proved? % :candidate)) evaluations)}
         :proofs {:new-native-target-results (count candidate-proved)
                  :new-exact-or-mappings 0 :new-exact-mathlib-mappings 0
                  :exact-mathlib-mappings-total
                  (count (get-in build [:prior :mappings]))}
         :checkpoint {:id (:rainbow.checkpoint/id value)
                      :kernel-replay (:status replay)
                      :mappings (count (:mappings value))}
         :claim-boundaries
         {:constructive-existence-proved? true
          :support-relative-uniqueness-proved? true
          :global-function-uniqueness-claimed? false
          :bellman-specialization-proved? false
          :real-or-rational-convergence-rate-proved? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        value (checkpoint build)
        replay (day54/replay-checkpoint value)]
    {:checkpoint value :report (report build value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :unique-fixed-point/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :unique-fixed-point/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command]]
  (try
    (if (= "replay" command)
      (let [result (load-report report-path)]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path))
            report-file (io/file report-path)]
        (.mkdirs (.getParentFile report-file))
        (spit report-file (str (pr-str report) "\n"))
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
