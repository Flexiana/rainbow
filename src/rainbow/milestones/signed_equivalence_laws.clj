(ns rainbow.milestones.signed-equivalence-laws
  "Held-out evidence for signed-rational equivalence transport laws."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.signed.equivalence-laws :as laws]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path "artifacts/signed-equivalence-laws/precommit.edn")
(def report-path "artifacts/signed-equivalence-laws/report.edn")
(def checkpoint-path "artifacts/signed-equivalence-laws/checkpoint.edn.gz")
(def default-input-checkpoint-path
  "artifacts/ahof/o32-coordinate-search/checkpoint.edn.gz")

(def target-names
  ['signed/equivalent-symmetric
   'signed/negate-respects-equivalence])

(def baseline-reuse-aliases
  ['nnrat/add-commutative
   'nnrat/equivalent-reflexive
   'nnrat/equivalent-symmetric
   'nnrat/equivalent-transitive
   'nnrat/add-respects-equivalence
   'signed/equivalent-reflexive])

(defn- resolved-ids [checked-environment aliases]
  (into #{} (keep #(environment/resolve-id checked-environment %)) aliases))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Signed equivalence precommit mismatch"
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
      (throw (ex-info "Signed equivalence input checkpoint rejected"
                      {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "Signed equivalence input checkpoint changed"
                      {:expected (get-in precommit
                                         [:precommit/source
                                          :input-checkpoint/id])
                       :actual (:checkpoint/id prior)})))
    (let [baseline-timed
          (timed #(commutative/extend-environment (:environment prior)))
          baseline (:value baseline-timed)
          candidate-timed (timed #(laws/extend-environment baseline))
          candidate (:value candidate-timed)
          theorem-ids (laws/theorem-ids candidate)
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
          common-reuse-ids (resolved-ids baseline baseline-reuse-aliases)
          baseline-index
          (timed #(reuse/build-index baseline {:include-ids common-reuse-ids}))
          candidate-index
          (timed #(reuse/build-index
                   candidate
                   {:include-ids (into common-reuse-ids (vals theorem-ids))}))
          baseline-search (timed #(evaluate baseline targets
                                            (:value baseline-index)))
          candidate-search (timed #(evaluate candidate targets
                                             (:value candidate-index)))]
      {:precommit precommit :prior prior :environment candidate
       :theorem-ids theorem-ids :targets targets
       :common-reuse-ids common-reuse-ids
       :baseline-build-wall-ms (:wall-ms baseline-timed)
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
             {:kind :signed-rational-equivalence-laws
              :precommit/id (get-in build [:precommit :precommit/id])
              :baseline-additions
              #{'nnrat/add-commutative 'nnrat/multiply-commutative
                'signed/add-commutative}
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
        held-base (count (filter #(proved? % :baseline) held-out))
        held-candidate (count (filter #(proved? % :candidate) held-out))
        baseline-states (mapv #(get-in % [:baseline :states-created]) evaluations)
        candidate-states (mapv #(get-in % [:candidate :states-created]) evaluations)
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        passed?
        (and (= :replayed (:status replay)) (= 2 (count candidate-proved))
             (= 1 held-candidate)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %)
                     (vals (:theorem-ids build))))
        newly-held (- held-candidate held-base)
        base
        {:status (if passed? :passed :failed)
         :source {:precommit/id (get-in build [:precommit :precommit/id])
                  :input-checkpoint/id (get-in build [:prior :checkpoint/id])
                  :baseline-capability-additions
                  #{'nnrat/add-commutative 'nnrat/multiply-commutative
                    'signed/add-commutative}
                  :reuse-index-scope
                  {:kind :precommitted-signed-equivalence-neighborhood
                   :common-declarations (count (:common-reuse-ids build))
                   :aliases (set baseline-reuse-aliases)}
                  :proof-values :native-only}
         :capability
         {:kind :signed-rational-equivalence-laws
          :representation :grothendieck-pairs-of-nonnegative-rationals
          :equality :additive-cross-equivalence
          :generalized-theorems (:theorem-ids build)
          :axiom-profiles axiom-profiles :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32 :depth-budget 64 :targets 2
          :baseline-proved (count baseline-proved)
          :candidate-proved (count candidate-proved)
          :held-out {:targets 1 :baseline-successes held-base
                     :candidate-successes held-candidate
                     :success-rate-change (- held-candidate held-base)}
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
          :timing {:baseline-environment-build-ms
                   (:baseline-build-wall-ms build)
                   :candidate-environment-build-ms
                   (:candidate-build-wall-ms build)
                   :baseline-reuse-index-ms (:baseline-index-wall-ms build)
                   :candidate-reuse-index-ms (:candidate-index-wall-ms build)
                   :baseline-search-wall-ms (:baseline-search-wall-ms build)
                   :candidate-search-wall-ms (:candidate-search-wall-ms build)
                   :ai-latency-ms :not-instrumented}
          :lemma-leverage
          {:definition :newly-solved-held-out-targets-per-total-introduction-cost
           :new-generalized-theorems 2
           :newly-solved-held-out-targets newly-held
           :held-out-targets-per-new-theorem (/ newly-held 2)
           :all-targets-per-new-theorem
           (/ (- (count candidate-proved) (count baseline-proved)) 2)
           :measured-rainbow-introduction-ms (:candidate-build-wall-ms build)
           :ai-inclusive-cost :not-instrumented}
          :evaluations evaluations
          :remaining-failures
          (filterv #(not (proved? % :candidate)) evaluations)}
         :proofs {:new-native-target-results
                  (- (count candidate-proved) (count baseline-proved))
                  :new-exact-or-mappings 0 :new-exact-mathlib-mappings 0
                  :exact-mathlib-mappings-total
                  (count (get-in build [:prior :mappings]))}
         :checkpoint {:id (:rainbow.checkpoint/id value)
                      :kernel-replay (:status replay)
                      :mappings (count (:mappings value))}
         :claim-boundaries
         {:transitivity-proved? false
          :signed-addition-congruence-proved? false
          :canonical-normalization-claimed? false
          :quotient-type-claimed? false
          :mathlib-mapping-credit? false
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
        {:status :rejected
         :error/category :signed-equivalence/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :signed-equivalence/report-read-failed
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
