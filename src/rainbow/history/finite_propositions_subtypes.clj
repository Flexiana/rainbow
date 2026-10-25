(ns rainbow.history.finite-propositions-subtypes
  "Finite propositions, subtype finiteness, and held-out subsingletons."
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
            [rainbow.history.finite-carriers :as finite-carriers]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.subtype :as finite-subtype]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day77/report.edn")
(def checkpoint-path "artifacts/day77/checkpoint.edn.gz")
(def default-input-checkpoint-path finite-carriers/checkpoint-path)
(def default-catalog-path or-curriculum-first-mapping/default-catalog-path)
(def default-statement-path or-curriculum-first-mapping/default-statement-path)
(def default-curriculum-path or-curriculum-first-mapping/default-curriculum-path)
(def default-validation-statement-path
  "artifacts/day77/validation-statements.edn")

;; The Day 77 record as it ran. Its instFiniteProp reproof was retracted in 1.4.2 (it used large
;; elimination from a proposition with several constructors, which the kernel now refuses); the
;; migrated checkpoint lists it under :retracted-mappings.
(def development-names ["instFiniteProp" "Set.Finite.eq_1"])
(def validation-names ["Finite.of_subsingleton"])
(def expected-gains (set (concat development-names validation-names)))

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
   :baseline (when (= :nativeized (:status baseline-target))
               (prove baseline-environment baseline-target baseline-options))
   :baseline-nativeization/status (:status baseline-target)
   :result (prove candidate-environment target candidate-options)})

(defn build [input-checkpoint-path statement-path curriculum-path
             validation-statement-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 77 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          partitions (into {} (map (juxt :foreign/name :study/partition))
                           (:or.curriculum/targets curriculum))
          development-batch
          (mathlib/verify-statement-batch default-catalog-path statement-path
                                          (statement-file-names statement-path))
          validation-batch
          (mathlib/verify-statement-batch default-catalog-path
                                          validation-statement-path
                                          validation-names)
          development-statements
          (filterv #(contains? (set development-names) (:foreign/name %))
                   (:statements development-batch))
          _ (when-not (= (set development-names)
                         (set (map :foreign/name development-statements)))
              (throw (ex-info "Day 77 development targets are absent"
                              {:targets development-statements})))
          statements (into development-statements
                           (:statements validation-batch))
          baseline-aliases
          (merge finite-sets/constant-aliases finite-type/constant-aliases)
          candidate-aliases
          (merge baseline-aliases finite-subtype/constant-aliases)
          baseline-targets
          (nativeize (:environment prior) baseline-aliases statements)
          support-environment
          (finite-subtype/extend-environment (:environment prior))
          candidate-targets
          (nativeize support-environment candidate-aliases statements)
          _ (when-not (every? #(= :nativeized (:status %)) candidate-targets)
              (throw (ex-info "Day 77 candidate target failed nativeization"
                              {:targets candidate-targets})))
          support-ids (finite-subtype/theorem-ids support-environment)
          principle-ids
          #{(environment/resolve-id support-environment 'logic/excluded-middle)
            (environment/resolve-id support-environment 'logic/proof-irrelevance)
            (environment/resolve-id support-environment
                                    'logic/proposition-extensionality)}
          reuse-index
          (reuse/build-index support-environment
                             {:include-ids (vals support-ids)})
          baseline-options preset-wide/candidate-options
          candidate-options
          (assoc preset-wide/candidate-options :reuse-index reuse-index
                 :reuse-policy {:allowed-axioms principle-ids})
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
                                     :finite-subtype-boundary
                                     "finite-subtype-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)]
      {:prior prior :curriculum curriculum
       :development-batch development-batch
       :validation-batch validation-batch
       :baseline-aliases baseline-aliases
       :candidate-aliases candidate-aliases
       :baseline-targets baseline-targets
       :candidate-targets candidate-targets
       :support-environment support-environment :support-ids support-ids
       :principle-ids principle-ids :reuse-index reuse-index
       :baseline-options baseline-options :candidate-options candidate-options
       :evaluations evaluations :proved proved
       :environment checked-environment :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :finite-subtype-boundary
         :development-statement-batch/id
         (get-in build [:development-batch :batch/id])
         :validation-statement-batch/id
         (get-in build [:validation-batch :batch/id])
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
        summary
        (mathlib/summarize catalog-path
                           (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build)
                                        (:mappings value))
        principle-by-alias
        (into {}
              (map (fn [alias]
                     [alias (environment/resolve-id (:environment build) alias)]))
              ['logic/excluded-middle 'logic/proof-irrelevance
               'logic/proposition-extensionality])
        expected-mapping-profiles
        {"instFiniteProp"
         #{(get principle-by-alias 'logic/excluded-middle)
           (get principle-by-alias 'logic/proof-irrelevance)}
         "Set.Finite.eq_1" (set (vals principle-by-alias))
         "Finite.of_subsingleton"
         #{(get principle-by-alias 'logic/excluded-middle)}}
        support-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:support-ids build))
        development-evaluations
        (filter #(contains? (set development-names)
                            (get-in % [:target :foreign/name]))
                (:evaluations build))
        validation-evaluation
        (first (filter #(= "Finite.of_subsingleton"
                           (get-in % [:target :foreign/name]))
                       (:evaluations build)))
        passed?
        (and (= :replayed (:status replay))
             (= expected-gains mapped-names)
             (= 3 (count mappings)
                (accounting/new-proof-objects mappings))
             (= expected-mapping-profiles
                (into {} (map (juxt :foreign/name :axioms)) mappings))
             (= #{:blocked}
                (set (map #(get-in % [:baseline :status])
                          development-evaluations)))
             (= :rejected (:baseline-nativeization/status
                            validation-evaluation))
             (every? #(= :proved (get-in % [:result :status]))
                     (:evaluations build))
             (every? #(= 2 (get-in % [:result :telemetry :states-created]))
                     (:evaluations build))
             (every? #(= 1 (get-in % [:result :telemetry :reuse-successes]))
                     (:evaluations build))
             (every? #(checked? (:environment build) %)
                     (concat (vals (finite-subtype/definition-ids
                                    (:environment build)))
                             (vals (:support-ids build))
                             (map :native/id mappings)))
             (= 1183 (:proved summary))
             (= 80 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:development-batch :catalog/id])
          :development-statement-batch/id
          (get-in build [:development-batch :batch/id])
          :validation-statement-batch/id
          (get-in build [:validation-batch :batch/id])
          :curriculum/id
          (get-in build [:curriculum :or.curriculum/id])}
         :nativeization
         {:instance-implicit-policy :normalize-to-implicit
          :type-subsingleton-definition
          (get (finite-subtype/definition-ids (:environment build))
               'type/subsingleton)
          :kernel-rechecked? true :trusted-kernel-change :none}
         :lemma-invention
         {:method :finite-proposition-and-subtype-boundary
          :theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true}
         :experiment
         {:development-targets (count development-evaluations)
          :held-out-targets 1
          :evaluations (mapv compact-evaluation (:evaluations build))}
         :proofs
         {:new-foreign-mappings (count mappings)
          :new-semantic-proof-objects
          (accounting/new-proof-objects mappings)
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
          :or-selected-exact-mappings
          (:exact-selected-mappings or-coverage)
          :or-selected-targets (:selected-targets or-coverage)}
         :claim-boundaries
         {:support-theorems-counted-as-foreign-proofs? false
          :direct-axiom-as-proof-count 0
          :new-proof-terms-kernel-rechecked? true
          :foreign-proof-values-present? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path statement-path curriculum-path
           validation-statement-path]
  (let [build (build input-checkpoint-path statement-path curriculum-path
                     validation-statement-path)
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
        {:status :rejected :error/category :day77/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day77/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command catalog-path statement-path curriculum-path
                validation-statement-path output-report-path
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
                 (or validation-statement-path
                     default-validation-statement-path))]
        (write-report! (or output-report-path report-path) report)
        (frontier/write-checkpoint! (or output-checkpoint-path checkpoint-path)
                                 checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
