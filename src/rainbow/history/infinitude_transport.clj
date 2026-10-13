(ns rainbow.history.infinitude-transport
  "Sort-polymorphic infinitude transport and faithful native integers."
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
            [rainbow.history.nat-infinitude :as nat-infinitude]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.infinite-transport :as infinite-transport]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day79/report.edn")
(def checkpoint-path "artifacts/day79/checkpoint.edn.gz")
(def default-input-checkpoint-path nat-infinitude/checkpoint-path)
(def default-catalog-path or-curriculum-first-mapping/default-catalog-path)
(def default-statement-path or-curriculum-first-mapping/default-statement-path)
(def default-curriculum-path or-curriculum-first-mapping/default-curriculum-path)
(def default-transport-statement-path
  "artifacts/day79/transport-statements.edn")

(def development-name "Int.infinite")
(def transport-names ["Infinite.of_surjective" "Infinite.of_injective"])
(def expected-gains #{development-name "Infinite.of_surjective"})
(def design-exposed-targets #{"Infinite.of_surjective"})

(defn- statement-file-names [path]
  (with-open [reader (io/reader path)]
    (->> (line-seq reader)
         (map edn/read-string)
         rest
         (mapv :foreign/name))))

(defn- nativeize [checked-environment aliases statements]
  (mapv #(ingest/nativeize-statement checked-environment % aliases) statements))

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn- evaluate [baseline-environment candidate-environment partitions
                 baseline-options candidate-options baseline-target target]
  {:target target
   :study/partition (get partitions (:foreign/name target))
   :design-exposed? (contains? design-exposed-targets (:foreign/name target))
   :baseline-nativeization/status (:status baseline-target)
   :baseline (when (= :nativeized (:status baseline-target))
               (prove baseline-environment baseline-target baseline-options))
   :result (prove candidate-environment target candidate-options)})

(defn build [input-checkpoint-path catalog-path statement-path curriculum-path
             transport-statement-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 79 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          partitions (into {} (map (juxt :foreign/name :study/partition))
                           (:or.curriculum/targets curriculum))
          development-batch
          (mathlib/verify-statement-batch
           catalog-path statement-path (statement-file-names statement-path))
          development-statement
          (first (filter #(= development-name (:foreign/name %))
                         (:statements development-batch)))
          _ (when-not development-statement
              (throw (ex-info "Day 79 Int target is absent from the OR batch"
                              {:error/category :day79/target-absent})))
          transport-batch
          (mathlib/verify-statement-batch catalog-path transport-statement-path
                                          transport-names)
          statements (into [development-statement]
                           (:statements transport-batch))
          baseline-aliases
          (merge finite-sets/constant-aliases finite-type/constant-aliases)
          baseline-targets
          (nativeize (:environment prior) baseline-aliases statements)
          support-environment
          (infinite-transport/extend-environment (:environment prior))
          candidate-aliases
          (merge baseline-aliases infinite-transport/constant-aliases)
          candidate-targets
          (nativeize support-environment candidate-aliases statements)
          _ (when-not (every? #(= :nativeized (:status %)) candidate-targets)
              (throw (ex-info "Day 79 candidate target failed nativeization"
                              {:targets candidate-targets})))
          support-ids (infinite-transport/theorem-ids support-environment)
          reuse-index
          (reuse/build-index
           support-environment
           {:include-ids
            [(get support-ids 'type/infinite-of-surjection)
             (get support-ids 'type/infinite-int)]})
          baseline-options preset-wide/candidate-options
          candidate-options
          (assoc preset-wide/candidate-options :reuse-index reuse-index
                 :reuse-policy {:allowed-axioms #{}})
          evaluations
          (->> (map vector baseline-targets candidate-targets)
               (pmap (fn [[baseline-target target]]
                       (evaluate (:environment prior) support-environment
                                 partitions baseline-options candidate-options
                                 baseline-target target)))
               doall vec)
          proved (filterv #(= :proved (get-in % [:result :status]))
                          evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :sort-polymorphic-infinite-transport
                                     "infinite-transport-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)]
      {:prior prior :curriculum curriculum
       :development-batch development-batch
       :transport-batch transport-batch :statements statements
       :baseline-aliases baseline-aliases
       :candidate-aliases candidate-aliases
       :baseline-targets baseline-targets
       :candidate-targets candidate-targets
       :support-environment support-environment
       :inductive-ids (infinite-transport/inductive-ids support-environment)
       :definition-ids (infinite-transport/definition-ids support-environment)
       :support-ids support-ids :reuse-index reuse-index
       :baseline-options baseline-options :candidate-options candidate-options
       :evaluations evaluations :proved proved
       :environment checked-environment :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :sort-polymorphic-infinite-transport
         :development-statement-batch/id
         (get-in build [:development-batch :batch/id])
         :transport-statement-batch/id
         (get-in build [:transport-batch :batch/id])
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
   :baseline-nativeization/status (:baseline-nativeization/status evaluation)
   :baseline/status (get-in evaluation [:baseline :status])
   :baseline/reason (get-in evaluation [:baseline :reason])
   :baseline/states-created
   (get-in evaluation [:baseline :telemetry :states-created])
   :candidate/status (get-in evaluation [:result :status])
   :candidate/reason (get-in evaluation [:result :reason])
   :candidate/states-created
   (get-in evaluation [:result :telemetry :states-created])
   :candidate/reuse-successes
   (get-in evaluation [:result :telemetry :reuse-successes])})

(defn report [catalog-path build value replay]
  (let [mappings (:new-mappings build)
        mapped-names (set (map :foreign/name mappings))
        summary (mathlib/summarize
                 catalog-path (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build) (:mappings value))
        evaluations-by-name
        (into {} (map (fn [evaluation]
                        [(get-in evaluation [:target :foreign/name]) evaluation]))
              (:evaluations build))
        support-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:support-ids build))
        successful-evaluations
        (map evaluations-by-name expected-gains)
        injective-evaluation (get evaluations-by-name "Infinite.of_injective")
        int-evaluation (get evaluations-by-name development-name)
        surjective-evaluation
        (get evaluations-by-name "Infinite.of_surjective")
        inductive-kinds
        (set (map #(get-in (:environment build)
                           [:rainbow.environment/declarations % :rainbow/kind])
                  (vals (:inductive-ids build))))
        passed?
        (and (= :replayed (:status replay))
             (= expected-gains mapped-names)
             (= 2 (count mappings) (accounting/new-proof-objects mappings))
             (every? empty? (map :axioms mappings))
             (= :rejected (:baseline-nativeization/status int-evaluation))
             (= :blocked (get-in surjective-evaluation [:baseline :status]))
             (every? #(= :proved (get-in % [:result :status]))
                     successful-evaluations)
             (every? #(= 2 (get-in % [:result :telemetry :states-created]))
                     successful-evaluations)
             (every? #(= 1 (get-in % [:result :telemetry :reuse-successes]))
                     successful-evaluations)
             (= :blocked (get-in injective-evaluation [:result :status]))
             (= #{:inductive :constructor :recursor} inductive-kinds)
             (every? empty? (vals support-profiles))
             (every? #(checked? (:environment build) %)
                     (concat (vals (:definition-ids build))
                             (vals (:support-ids build))
                             (map :native/id mappings)))
             (= 1186 (:proved summary))
             (= 83 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:development-batch :catalog/id])
          :development-statement-batch/id
          (get-in build [:development-batch :batch/id])
          :transport-statement-batch/id
          (get-in build [:transport-batch :batch/id])
          :curriculum/id (get-in build [:curriculum :or.curriculum/id])}
         :representation
         {:method :faithful-two-constructor-integer
          :inductive-declarations (:inductive-ids build)
          :definitions (:definition-ids build)
          :foreign-concept-map infinite-transport/constant-aliases
          :kernel-rechecked? true :trusted-kernel-change :none}
         :lemma-invention
         {:method :sort-polymorphic-finite-image-transport
          :theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true}
         :experiment
         {:state-budget (:states preset-wide/candidate-options)
          :evaluations (mapv compact-evaluation (:evaluations build))
          :partition-integrity
          {:design-exposed-targets design-exposed-targets
           :transfer-result-used-as-promotion-evidence? false
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
          :design-exposed-transfer-counted-as-validation? false
          :direct-axiom-as-proof-count 0
          :new-proof-terms-kernel-rechecked? true
          :foreign-proof-values-present? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path statement-path curriculum-path
           transport-statement-path]
  (let [build (build input-checkpoint-path catalog-path statement-path
                     curriculum-path transport-statement-path)
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
        {:status :rejected :error/category :day79/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day79/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command catalog-path statement-path curriculum-path
                transport-statement-path output-report-path
                output-checkpoint-path]]
  (try
    (if (= "replay" command)
      (let [result (load-report (or catalog-path report-path))]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path)
                 (or catalog-path default-catalog-path)
                 (or statement-path default-statement-path)
                 (or curriculum-path default-curriculum-path)
                 (or transport-statement-path
                     default-transport-statement-path))]
        (write-report! (or output-report-path report-path) report)
        (frontier/write-checkpoint! (or output-checkpoint-path checkpoint-path)
                                 checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
