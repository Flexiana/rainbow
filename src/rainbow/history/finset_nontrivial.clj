(ns rainbow.history.finset-nontrivial
  "Nontrivial Finsets through the existing extensional Set concept."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.accounting :as accounting]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.history.or-curriculum-first-mapping :as or-curriculum-first-mapping]
            [rainbow.history.finset-carriers :as finset-carriers]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.subtype :as finite-subtype]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.finset :as finset]
            [rainbow.math.sets.finset.nontrivial :as finset-nontrivial]
            [rainbow.math.logic.fintype :as fintype]
            [rainbow.math.logic.infinite-transport :as infinite-transport]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day84/report.edn")
(def checkpoint-path "artifacts/day84/checkpoint.edn.gz")
(def default-input-checkpoint-path finset-carriers/checkpoint-path)
(def default-catalog-path or-curriculum-first-mapping/default-catalog-path)
(def default-curriculum-path or-curriculum-first-mapping/default-curriculum-path)
(def default-statement-path
  "artifacts/day84/finset-nontrivial-statements.edn")

(def target-support
  {"Finset.Nontrivial.nonempty" 'finset/nontrivial-nonempty
   "Finset.not_nontrivial_empty._simp_1"
   'finset/empty-nontrivial-proposition-equality
   "Finset.not_nontrivial_singleton" 'finset/singleton-not-nontrivial
   "Finset.not_nontrivial_empty" 'finset/empty-not-nontrivial})

(def target-names (vec (keys target-support)))
(def design-exposed-targets (set target-names))

(def prior-aliases
  (merge finite-sets/constant-aliases
         finite-type/constant-aliases
         finite-subtype/constant-aliases
         infinite-transport/constant-aliases
         finset/constant-aliases
         fintype/constant-aliases))

(defn- nativeize [checked-environment aliases statements]
  (mapv #(ingest/nativeize-statement checked-environment % aliases)
        statements))

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn build [input-checkpoint-path catalog-path statement-path curriculum-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 84 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          partitions (into {} (map (juxt :foreign/name :study/partition))
                           (:or.curriculum/targets curriculum))
          batch (mathlib/verify-statement-batch catalog-path statement-path
                                                target-names)
          baseline-targets
          (nativeize (:environment prior) prior-aliases (:statements batch))
          _ (when-not (every? #(= :rejected (:status %)) baseline-targets)
              (throw (ex-info "Day 84 baseline unexpectedly nativeized nontrivial"
                              {:targets baseline-targets})))
          support-environment
          (finset-nontrivial/extend-environment (:environment prior))
          aliases (merge prior-aliases finset-nontrivial/constant-aliases)
          candidate-targets
          (nativeize support-environment aliases (:statements batch))
          _ (when-not (every? #(= :nativeized (:status %)) candidate-targets)
              (throw (ex-info "Day 84 candidate target failed nativeization"
                              {:targets candidate-targets})))
          definition-ids
          (finset-nontrivial/definition-ids support-environment)
          support-ids (finset-nontrivial/theorem-ids support-environment)
          reuse-ids (mapv #(get support-ids (get target-support %)) target-names)
          reuse-index (reuse/build-index support-environment
                                         {:include-ids reuse-ids})
          allowed-axioms
          (set (map #(environment/resolve-id support-environment %)
                    ['logic/excluded-middle
                     'logic/function-extensionality
                     'logic/proposition-extensionality
                     'logic/proof-irrelevance]))
          candidate-options
          (assoc preset-wide/candidate-options :reuse-index reuse-index
                 :reuse-policy {:allowed-axioms allowed-axioms})
          evaluations
          (->> candidate-targets
               (pmap
                (fn [target]
                  {:target target
                   :study/partition (get partitions (:foreign/name target))
                   :design-exposed? true
                   :baseline/nativeization
                   (first (filter #(= (:foreign/name target)
                                      (:foreign/name %))
                                  baseline-targets))
                   :result (prove support-environment target candidate-options)}))
               doall vec)
          proved (filterv #(= :proved (get-in % [:result :status]))
                          evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :finset-set-nontrivial-bridge
                                     "finset-nontrivial-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)]
      {:prior prior :curriculum curriculum :batch batch
       :baseline-targets baseline-targets :candidate-targets candidate-targets
       :support-environment support-environment :aliases aliases
       :definition-ids definition-ids :support-ids support-ids
       :reuse-index reuse-index :allowed-axioms allowed-axioms
       :candidate-options candidate-options :evaluations evaluations
       :proved proved :environment checked-environment
       :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :finset-set-nontrivial-bridge
         :statement-batch/id (get-in build [:batch :batch/id])
         :design-exposed-targets design-exposed-targets
         :curriculum/id (get-in build [:curriculum :or.curriculum/id])
         :proof-values :redacted}
        base (-> value
                 (dissoc :rainbow.checkpoint/id)
                 (update-in [:source :additional-statement-batches]
                            (fnil conj []) extra-source))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status (kernel/check checked-environment
                              (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))))

(defn- compact-evaluation [evaluation]
  {:foreign/name (get-in evaluation [:target :foreign/name])
   :study/partition (:study/partition evaluation)
   :design-exposed? (:design-exposed? evaluation)
   :baseline-nativeization/status
   (get-in evaluation [:baseline/nativeization :status])
   :baseline-nativeization/error-category
   (get-in evaluation [:baseline/nativeization :error :error/category])
   :candidate-nativeization/status :nativeized
   :candidate/status (get-in evaluation [:result :status])
   :candidate/reason (get-in evaluation [:result :reason])
   :candidate/states-created
   (get-in evaluation [:result :telemetry :states-created])
   :candidate/reuse-successes
   (get-in evaluation [:result :telemetry :reuse-successes])})

(defn report [catalog-path build value replay]
  (let [mappings (:new-mappings build)
        mapped-names (set (map :foreign/name mappings))
        proof-ids (set (map :proof/id mappings))
        summary (mathlib/summarize
                 catalog-path (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build) (:mappings value))
        support-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:support-ids build))
        all-ids (concat (vals (:definition-ids build))
                        (vals (:support-ids build))
                        (map :native/id mappings))
        passed?
        (and (= :replayed (:status replay))
             (= design-exposed-targets mapped-names)
             (= 4 (count mappings) (count proof-ids))
             (= 4 (count (:baseline-targets build))
                    (count (:candidate-targets build)))
             (every? #(= :rejected (:status %)) (:baseline-targets build))
             (every? #(= :nativeized (:status %)) (:candidate-targets build))
             (every? #(= :proved (get-in % [:result :status]))
                     (:evaluations build))
             (every? #(= 2 (get-in % [:result :telemetry :states-created]))
                     (:evaluations build))
             (every? #(= 1 (get-in % [:result :telemetry :reuse-successes]))
                     (:evaluations build))
             (every? #(checked? (:environment build) %) all-ids)
             (= 1216 (:proved summary))
             (= 113 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:batch :catalog/id])
          :statement-batch/id (get-in build [:batch :batch/id])
          :curriculum/id (get-in build [:curriculum :or.curriculum/id])}
         :representation
         {:method :finset-set-nontrivial-view
          :native-shape :two-distinct-members-of-extensional-predicate
          :foreign-shape :finset-nontrivial-predicate
          :definitions (:definition-ids build)
          :definitions-counted-as-proofs? false
          :kernel-rechecked? true :trusted-kernel-change :none}
         :lemma-invention
         {:method :finset-nontrivial-empty-singleton-family
          :theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true}
         :experiment
         {:state-budget (:states preset-wide/candidate-options)
          :baseline-nativeizable 0 :candidate-nativeizable 4
          :evaluations (mapv compact-evaluation (:evaluations build))
          :partition-integrity
          {:design-exposed-targets design-exposed-targets
           :held-out-result-used-as-validation? false
           :valid-held-out-or-transfer-gain 0}}
         :proofs
         {:new-foreign-mappings (count mappings)
          :new-semantic-proof-objects (accounting/new-proof-objects mappings)
          :new-axiom-profiles (frequencies (map :axioms mappings))
          :mappings mappings}
         :checkpoint
         {:id (:rainbow.checkpoint/id value)
          :kernel-replay (:status replay)
          :mappings (count (:mappings value))}
         :coverage
         {:exact-statement-mappings (:proved summary)
          :theorem-declarations (:theorems summary)
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :or-selected-exact-mappings (:exact-selected-mappings or-coverage)
          :or-selected-targets (:selected-targets or-coverage)}
         :claim-boundaries
         {:support-theorems-counted-as-foreign-proofs? false
          :design-exposed-held-out-counted-as-validation? false
          :direct-axiom-as-proof-count 0
          :new-proof-terms-kernel-rechecked? true
          :foreign-proof-values-present? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path statement-path curriculum-path]
  (let [build (build input-checkpoint-path catalog-path statement-path
                     curriculum-path)
        value (checkpoint build)
        replay (checkpoint/replay-checkpoint value)]
    {:build build :checkpoint value :replay replay
     :report (report catalog-path build value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :day84/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day84/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command catalog-path statement-path curriculum-path
                output-report-path output-checkpoint-path]]
  (try
    (if (= "replay" command)
      (let [result (load-report (or catalog-path report-path))]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path)
                 (or catalog-path default-catalog-path)
                 (or statement-path default-statement-path)
                 (or curriculum-path default-curriculum-path))]
        (write-report! (or output-report-path report-path) report)
        (frontier/write-checkpoint! (or output-checkpoint-path checkpoint-path)
                                 checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
