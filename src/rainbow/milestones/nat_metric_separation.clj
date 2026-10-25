(ns rainbow.milestones.nat-metric-separation
  "Equal-resource evidence for constructive Nat metric separation."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.distance :as nat-distance]
            [rainbow.math.nat.metric-separation :as separation]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path
  "artifacts/nat-metric-separation-mathlib/precommit.edn")
(def statement-path
  "artifacts/nat-metric-separation-mathlib/statements.edn")
(def report-path
  "artifacts/nat-metric-separation-mathlib/report.edn")
(def checkpoint-path
  "artifacts/nat-metric-separation-mathlib/checkpoint.edn.gz")
(def default-input-checkpoint-path
  "artifacts/nat-distance-core-mathlib/checkpoint.edn.gz")
(def default-catalog-path
  "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")

(def generalized-theorem-names
  '[nat/positive-of-nonzero
    nat/nonzero-of-positive
    nat/distance-nonzero-of-not-equal
    nat/distance-positive-of-not-equal])

(def held-out-native-theorem-names
  '[nat/distance-positive-equivalent-not-equal])

(def constant-aliases
  (merge finite-sets/constant-aliases
         nat-distance/constant-aliases
         finset-range/constant-aliases))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Nat metric-separation precommit identity mismatch"
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

(defn- evaluate [checked-environment target search-options]
  {:target target
   :study/partition :held-out
   :result
   (when (= :nativeized (:status target))
     (prove checked-environment target search-options))})

(defn build [input-checkpoint-path catalog-path]
  (let [precommit (load-precommit)
        names (mapv :foreign/name (:precommit/targets precommit))
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Nat metric-separation input checkpoint rejected"
                      {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "Nat metric-separation input checkpoint changed"
                      {:expected
                       (get-in precommit
                               [:precommit/source :input-checkpoint/id])
                       :actual (:checkpoint/id prior)})))
    (let [batch
          (mathlib/verify-statement-batch catalog-path statement-path names)
          _ (when-not
             (= (get-in precommit [:precommit/source :statement-batch/id])
                (:batch/id batch))
              (throw
               (ex-info "Nat metric-separation batch changed after precommit"
                        {:expected
                         (get-in precommit
                                 [:precommit/source :statement-batch/id])
                         :actual (:batch/id batch)})))
          baseline-environment (:environment prior)
          baseline-nativeization
          (timed #(nativeize baseline-environment (:statements batch)))
          baseline-options (options baseline-environment [])
          baseline-evaluations
          (timed
           #(mapv (fn [target]
                    (evaluate baseline-environment target baseline-options))
                  (:value baseline-nativeization)))
          candidate-environment-build
          (timed #(separation/extend-environment baseline-environment))
          support-environment (:value candidate-environment-build)
          theorem-ids (separation/theorem-ids support-environment)
          candidate-options
          (options support-environment generalized-theorem-names)
          candidate-nativeization
          (timed #(nativeize support-environment (:statements batch)))
          candidate-evaluations
          (timed
           #(mapv (fn [target]
                    (evaluate support-environment target candidate-options))
                  (:value candidate-nativeization)))
          evaluations (:value candidate-evaluations)
          proved
          (filterv #(= :proved (get-in % [:result :status])) evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result
                    current evaluation
                    :constructive-nat-metric-separation
                    "nat-metric-separation-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []]
           proved)]
      {:precommit precommit
       :prior prior
       :batch batch
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
        {:kind :constructive-nat-metric-separation
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
     :reuse-candidates (get-in result [:telemetry :reuse-candidates] 0)
     :reuse-attempts (get-in result [:telemetry :reuse-attempts] 0)
     :reuse-successes (get-in result [:telemetry :reuse-successes] 0)}))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn report [catalog-path build value replay]
  (let [baseline (mapv compact-evaluation (:baseline-evaluations build))
        candidate (mapv compact-evaluation (:evaluations build))
        baseline-proved (filterv #(= :proved (:status %)) baseline)
        candidate-proved (filterv #(= :proved (:status %)) candidate)
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        generalized-theorems
        (select-keys (:theorem-ids build) generalized-theorem-names)
        held-out-native-theorems
        (select-keys (:theorem-ids build) held-out-native-theorem-names)
        summary
        (mathlib/summarize
         catalog-path (set (map :foreign/name (:mappings value))))
        passed?
        (and (= :replayed (:status replay))
             (= :verified (get-in build [:batch :status]))
             (= 1 (count baseline))
             (zero? (count baseline-proved))
             (= 1 (count candidate-proved))
             (= 1 (count (:new-mappings build)))
             (every? empty? (vals axiom-profiles))
             (every? #(checked? (:environment build) %)
                     (vals (:theorem-ids build)))
             (every? #(checked? (:environment build) %)
                     (map :native/id (:new-mappings build))))
        newly-solved (- (count candidate-proved) (count baseline-proved))
        introduction-cost
        (+ (:environment-build-wall-ms build)
           (:candidate-search-wall-ms build))
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
         {:kind :constructive-natural-metric-separation
          :generalized-theorems generalized-theorems
          :held-out-native-theorems held-out-native-theorems
          :axiom-profiles axiom-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32
          :depth-budget 64
          :targets 1
          :baseline-proved (count baseline-proved)
          :candidate-proved (count candidate-proved)
          :held-out
          {:targets 1
           :baseline-successes (count baseline-proved)
           :candidate-successes (count candidate-proved)
           :success-rate-change newly-solved}
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
          {:total-states (reduce + (map :states-created candidate-proved))
           :total-search-wall-ms
           (reduce + (map :wall-ms candidate-proved))}
          :lemma-leverage
          {:new-generalized-lemmas (count generalized-theorems)
           :newly-solved-held-out-targets newly-solved
           :held-out-targets-per-generalized-theorem
           (/ newly-solved (count generalized-theorems))
           :total-introduction-cost-ms introduction-cost
           :newly-solved-targets-per-cost-ms
           (when (pos? introduction-cost)
             (/ newly-solved introduction-cost))}
          :baseline-evaluations baseline
          :candidate-evaluations candidate
          :remaining-failures
          (filterv #(not= :proved (:status %)) candidate)}
         :proofs
         {:new-native-results (count (:theorem-ids build))
          :new-generalized-theorems (count generalized-theorems)
          :new-held-out-native-theorems
          (count held-out-native-theorems)
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
          :native-held-out-result-counted-as-foreign-proof? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path]
  (let [build (build input-checkpoint-path catalog-path)
        value (checkpoint build)
        replay (day54/replay-checkpoint value)]
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
         :error/category :nat-metric-separation/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :nat-metric-separation/report-read-failed
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
