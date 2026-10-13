(ns rainbow.milestones.nat-distance-core
  "Equal-resource evidence for the proof-redacted Mathlib Nat-distance core."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.distance :as nat-distance]
            [rainbow.math.nat.distance-core :as distance-core]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path
  "artifacts/nat-distance-core-mathlib/precommit.edn")
(def statement-path
  "artifacts/nat-distance-core-mathlib/statements.edn")
(def report-path
  "artifacts/nat-distance-core-mathlib/report.edn")
(def checkpoint-path
  "artifacts/nat-distance-core-mathlib/checkpoint.edn.gz")
(def default-input-checkpoint-path
  "artifacts/or-rational-iteration/checkpoint.edn.gz")
(def default-catalog-path
  "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")

(def target-support
  {"Nat.dist_zero_left" 'nat/distance-zero-left
   "Nat.dist_zero_right" 'nat/distance-zero-right
   "Nat.dist_self" 'nat/distance-self
   "Nat.eq_of_dist_eq_zero" 'nat/equal-of-distance-zero
   "Nat.dist_eq_zero" 'nat/distance-zero-of-equal
   "Nat.dist_mul_right" 'nat/distance-multiply-right
   "Nat.dist_mul_left" 'nat/distance-multiply-left})

(def generalized-theorem-names
  '[nat/distance-zero-left
    nat/distance-zero-right
    nat/distance-self
    nat/equal-of-distance-zero
    nat/distance-zero-equivalent-equal])

(def support-certificate-names
  '[nat/distance-zero-of-equal])

(def prior-support
  '[nat/distance-successor
    nat/distance-commutative
    nat/distance-add-left
    nat/distance-add-right
    nat/distance-right-bound
    nat/distance-left-bound
    nat/distance-triangle
    nat/distance-multiply-right
    nat/distance-multiply-left])

(def constant-aliases
  (merge
   finite-sets/constant-aliases
   nat-distance/constant-aliases
   {"HMul.hMul" 'algebra/heterogeneous-add
    "instHMul" 'algebra/homogeneous-add-instance
    "instMulNat" 'nat/multiply}))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Nat-distance-core precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- nativeize [checked-environment statements]
  (mapv #(ingest/nativeize-statement checked-environment
                                    % constant-aliases)
        statements))

(defn- support-ids [checked-environment aliases]
  (mapv #(environment/resolve-id checked-environment %) aliases))

(defn- options [checked-environment aliases]
  (assoc preset-wide/candidate-options
         :states 32
         :depth 64
         :reuse-index
         (reuse/build-index
          checked-environment
          {:include-ids (support-ids checked-environment aliases)})
         :reuse-policy {:allowed-axioms #{}}))

(defn- prove [checked-environment target search-options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   search-options))

(defn- evaluate
  [checked-environment partitions targets search-options]
  (mapv
   (fn [target]
     {:target target
      :study/partition (get partitions (:foreign/name target))
      :result
      (when (= :nativeized (:status target))
        (prove checked-environment target search-options))})
   targets))

(defn build [input-checkpoint-path catalog-path]
  (let [precommit (load-precommit)
        names (mapv :foreign/name (:precommit/targets precommit))
        partitions (into {} (map (juxt :foreign/name :study/partition))
                         (:precommit/targets precommit))
        prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Nat-distance-core input checkpoint rejected"
                      {:prior prior})))
    (let [batch
          (mathlib/verify-statement-batch catalog-path statement-path names)
          _ (when-not
             (= (get-in precommit [:precommit/source :statement-batch/id])
                (:batch/id batch))
              (throw
               (ex-info "Nat-distance-core batch changed after precommit"
                        {:expected
                         (get-in precommit
                                 [:precommit/source :statement-batch/id])
                         :actual (:batch/id batch)})))
          baseline-environment (:environment prior)
          baseline-nativeization
          (timed #(nativeize baseline-environment (:statements batch)))
          baseline-options (options baseline-environment prior-support)
          baseline-evaluations
          (timed
           #(evaluate baseline-environment partitions
                      (:value baseline-nativeization) baseline-options))
          candidate-environment-build
          (timed #(distance-core/extend-environment baseline-environment))
          support-environment (:value candidate-environment-build)
          theorem-ids (distance-core/theorem-ids support-environment)
          candidate-options
          (options support-environment
                   (into prior-support generalized-theorem-names))
          candidate-nativeization
          (timed #(nativeize support-environment (:statements batch)))
          candidate-evaluations
          (timed
           #(evaluate support-environment partitions
                      (:value candidate-nativeization) candidate-options))
          evaluations (:value candidate-evaluations)
          proved
          (filterv #(= :proved (get-in % [:result :status])) evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result
                    current evaluation
                    :constructive-nat-distance-core
                    "nat-distance-core-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []]
           proved)]
      {:precommit precommit
       :prior prior
       :batch batch
       :partitions partitions
       :baseline-environment baseline-environment
       :baseline-targets (:value baseline-nativeization)
       :baseline-nativeization-wall-ms (:wall-ms baseline-nativeization)
       :baseline-options baseline-options
       :baseline-evaluations (:value baseline-evaluations)
       :baseline-search-wall-ms (:wall-ms baseline-evaluations)
       :support-environment support-environment
       :environment-build-wall-ms (:wall-ms candidate-environment-build)
       :theorem-ids theorem-ids
       :candidate-options candidate-options
       :candidate-targets (:value candidate-nativeization)
       :candidate-nativeization-wall-ms (:wall-ms candidate-nativeization)
       :evaluations evaluations
       :candidate-search-wall-ms (:wall-ms candidate-evaluations)
       :proved proved
       :environment checked-environment
       :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :constructive-nat-distance-core
         :precommit/id (get-in build [:precommit :precommit/id])
         :statement-batch/id (get-in build [:batch :batch/id])
         :target-names
         (set (map :foreign/name
                   (get-in build [:precommit :precommit/targets])))
         :proof-values :redacted}
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in [:source :additional-statement-batches]
                       (fnil conj []) extra-source))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn- compact-evaluation [evaluation]
  (let [target (:target evaluation)
        result (:result evaluation)]
    {:foreign/name (:foreign/name target)
     :study/partition (:study/partition evaluation)
     :nativeization-status (:status target)
     :nativeization-error (get-in target [:error :error/category])
     :status (or (:status result) :not-run)
     :reason (:reason result)
     :states-created (get-in result [:telemetry :states-created] 0)
     :wall-ms (get-in result [:telemetry :wall-ms] 0)
     :reuse-successes (get-in result [:telemetry :reuse-successes] 0)}))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- median [numbers]
  (when (seq numbers)
    (let [ordered (vec (sort numbers))]
      (nth ordered (quot (count ordered) 2)))))

(defn report [catalog-path build value replay]
  (let [baseline (mapv compact-evaluation (:baseline-evaluations build))
        candidate (mapv compact-evaluation (:evaluations build))
        baseline-proved (filterv #(= :proved (:status %)) baseline)
        candidate-proved (filterv #(= :proved (:status %)) candidate)
        held-out (filterv #(= :held-out (:study/partition %)) candidate)
        baseline-held-out
        (filterv #(= :held-out (:study/partition %)) baseline)
        held-out-proved
        (count (filter #(= :proved (:status %)) held-out))
        baseline-held-out-proved
        (count (filter #(= :proved (:status %)) baseline-held-out))
        states (mapv :states-created candidate-proved)
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        generalized-theorems
        (select-keys (:theorem-ids build) generalized-theorem-names)
        support-certificates
        (select-keys (:theorem-ids build) support-certificate-names)
        summary
        (mathlib/summarize
         catalog-path (set (map :foreign/name (:mappings value))))
        passed?
        (and (= :replayed (:status replay))
             (= :verified (get-in build [:batch :status]))
             (= 7 (count candidate))
             (= 3 (count baseline-proved))
             (= 7 (count candidate-proved))
             (= 7 (count (:new-mappings build)))
             (zero? baseline-held-out-proved)
             (= 2 held-out-proved)
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %)
                     (vals (:theorem-ids build)))
             (every? #(checked? (:environment build) %)
                     (map :native/id (:new-mappings build))))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib
          :version mathlib/pinned-version
          :commit mathlib/pinned-commit
          :proof-values :redacted
          :catalog/id (get-in build [:batch :catalog/id])
          :statement-batch/id (get-in build [:batch :batch/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :capability
         {:kind :constructive-natural-distance-separation
          :generalized-theorems generalized-theorems
          :support-certificates support-certificates
          :axiom-profiles axiom-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32
          :depth-budget 64
          :targets 7
          :baseline-proved (count baseline-proved)
          :candidate-proved (count candidate-proved)
          :held-out
          {:targets (count held-out)
           :baseline-successes baseline-held-out-proved
           :candidate-successes held-out-proved
           :success-rate-change
           (/ (- held-out-proved baseline-held-out-proved)
              (count held-out))}
          :timing
          {:environment-build-ms (:environment-build-wall-ms build)
           :baseline-nativeization-ms
           (:baseline-nativeization-wall-ms build)
           :baseline-search-ms (:baseline-search-wall-ms build)
           :candidate-nativeization-ms
           (:candidate-nativeization-wall-ms build)
           :candidate-search-ms (:candidate-search-wall-ms build)
           :ai-latency-ms :not-instrumented}
          :search-cost
          {:median-states (median states)
           :total-states (reduce + states)
           :total-search-wall-ms
           (reduce + (map :wall-ms candidate-proved))}
          :lemma-leverage
          {:new-generalized-lemmas (count generalized-theorems)
           :newly-solved-held-out-targets
           (- held-out-proved baseline-held-out-proved)
           :held-out-targets-per-generalized-theorem
           (/ (- held-out-proved baseline-held-out-proved)
              (count generalized-theorems))
           :total-introduction-cost-ms
           (+ (:environment-build-wall-ms build)
              (:candidate-search-wall-ms build))}
          :baseline-evaluations baseline
          :candidate-evaluations candidate
          :remaining-failures
          (filterv #(not= :proved (:status %)) candidate)}
         :proofs
         {:new-native-results (count (:theorem-ids build))
          :new-generalized-theorems (count generalized-theorems)
          :new-support-certificates (count support-certificates)
          :new-exact-mathlib-mappings (count (:new-mappings build))
          :new-axiom-profiles
          (frequencies (map :axioms (:new-mappings build)))
          :mappings (:new-mappings build)}
         :checkpoint
         {:id (:rainbow.checkpoint/id value)
          :kernel-replay (:status replay)
          :mappings (count (:mappings value))}
         :coverage
         {:exact-statement-mappings (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))}
         :claim-boundaries
         {:proof-redacted-evaluation? true
          :lean-proof-bodies-imported? false
          :support-theorems-counted-as-foreign-proofs? false
          :typed-natural-literal-zero-only? true
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path]
  (let [build (build input-checkpoint-path catalog-path)
        value (checkpoint build)
        replay (checkpoint/replay-checkpoint value)]
    {:build build
     :checkpoint value
     :replay replay
     :report (report catalog-path build value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :nat-distance-core/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :nat-distance-core/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command catalog-path]]
  (try
    (if (= "replay" command)
      (let [result (load-report (or catalog-path report-path))]
        (println (pr-str result))
        (when-not (= :replayed (:status result))
          (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path)
                 (or catalog-path default-catalog-path))]
        (write-report! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report))
          (System/exit 1))))
    (finally (shutdown-agents))))
