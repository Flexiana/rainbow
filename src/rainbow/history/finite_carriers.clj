(ns rainbow.history.finite-carriers
  "Finite-carrier representations and universal-set bridge reuse."
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
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day76/report.edn")
(def checkpoint-path "artifacts/day76/checkpoint.edn.gz")
(def default-input-checkpoint-path or-curriculum-first-mapping/checkpoint-path)
(def default-catalog-path or-curriculum-first-mapping/default-catalog-path)
(def default-statement-path or-curriculum-first-mapping/default-statement-path)
(def default-curriculum-path or-curriculum-first-mapping/default-curriculum-path)
(def default-validation-statement-path
  "/tmp/rainbow-or40-finite-validation-statements.edn")

(def expected-gains
  #{"fintypeOfNotInfinite._proof_1" "Set.infinite_univ_iff"
    "Set.finite_univ_iff" "Finite.of_finite_univ" "infinite_prod"})

(def validation-names
  ["Infinite.of_not_fintype" "Set.finite_lt_nat"
   "Set.univ_finite_iff_nonempty_fintype" "Set.Infinite.sUnion"
   "Finset.finite_toSet" "Multiset.finite_toSet"
   "Finset.finite_toSet_toFinset" "Infinite.of_surjective_from_set"
   "Set.Finite.injOn_iff_bijOn_of_mapsTo" "infinite_prod"
   "Set.union_finset_finite_of_range_finite"])

(defn- nativeize [checked-environment aliases statements]
  (mapv #(ingest/nativeize-statement checked-environment % aliases) statements))

(defn- prove-target [checked-environment partitions options target]
  {:target target
   :study/partition (get partitions (:foreign/name target))
   :result
   (search/prove
    (:state (proof/start checked-environment (:type target)
                         {:universes (:universes target)}))
    options)})

(defn build [input-checkpoint-path statement-path curriculum-path
             validation-statement-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 76 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          ;; Reuse the exact pre-Day-75 batch rather than sliding its window
          ;; after the first mapping was accepted.
          selection-mappings
          (remove #(= or-curriculum-first-mapping/target-name (:foreign/name %)) (:mappings prior))
          selected (or40/next-proof-batch curriculum selection-mappings)
          names (mapv :foreign/name selected)
          partitions (into {} (map (juxt :foreign/name :study/partition))
                           (:or.curriculum/targets curriculum))
          batch (mathlib/verify-statement-batch default-catalog-path
                                                statement-path names)
          baseline-results
          (nativeize (:environment prior) finite-sets/constant-aliases
                     (:statements batch))
          baseline-native-names
          (set (map :foreign/name
                    (filter #(= :nativeized (:status %)) baseline-results)))
          support-environment
          (finite-type/extend-environment (:environment prior))
          aliases (merge finite-sets/constant-aliases finite-type/constant-aliases)
          candidate-results
          (nativeize support-environment aliases (:statements batch))
          targets
          (->> candidate-results
               (filter #(and (= :nativeized (:status %))
                             (not (contains? baseline-native-names
                                             (:foreign/name %)))))
               vec)
          support-ids (finite-type/theorem-ids support-environment)
          excluded-middle-id
          (environment/resolve-id support-environment 'logic/excluded-middle)
          reuse-index
          (reuse/build-index support-environment
                             {:include-ids (vals support-ids)})
          search-options
          (assoc preset-wide/candidate-options :reuse-index reuse-index
                 :reuse-policy {:allowed-axioms #{excluded-middle-id}})
          evaluations
          (->> targets
               (pmap #(prove-target support-environment partitions
                                    search-options %))
               doall vec)
          proved (filterv #(= :proved (get-in % [:result :status]))
                          evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :finite-carrier-universal-bridge
                                     "finite-carrier-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)
          validation-batch
          (mathlib/verify-statement-batch default-catalog-path
                                          validation-statement-path
                                          validation-names)
          validation-baseline
          (nativeize (:environment prior) finite-sets/constant-aliases
                     (:statements validation-batch))
          validation-old-names
          (set (map :foreign/name
                    (filter #(= :nativeized (:status %)) validation-baseline)))
          validation-candidate
          (nativeize support-environment aliases (:statements validation-batch))
          validation-targets
          (filterv #(and (= :nativeized (:status %))
                         (not (contains? validation-old-names
                                         (:foreign/name %))))
                   validation-candidate)
          validation-evaluations
          (->> validation-targets
               (pmap #(prove-target support-environment partitions
                                    search-options %))
               doall vec)
          validation-proved
          (filterv #(= :proved (get-in % [:result :status]))
                   validation-evaluations)
          [final-environment validation-mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :finite-carrier-product-bridge
                                     "finite-carrier-validation-")]
               [next-environment (conj accepted mapping)]))
           [checked-environment []] validation-proved)
          all-mappings (into mappings validation-mappings)]
      {:prior prior :curriculum curriculum :selected selected :batch batch
       :baseline-results baseline-results :candidate-results candidate-results
       :support-environment support-environment :aliases aliases
       :targets targets :support-ids support-ids
       :excluded-middle-id excluded-middle-id :reuse-index reuse-index
       :search-options search-options :evaluations evaluations :proved proved
       :environment final-environment :new-mappings all-mappings
       :validation-batch validation-batch
       :validation-baseline validation-baseline
       :validation-candidate validation-candidate
       :validation-targets validation-targets
       :validation-evaluations validation-evaluations
       :validation-proved validation-proved
       :validation-mappings validation-mappings})))

(defn checkpoint [build]
  (frontier/checkpoint build))

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
   :status (get-in evaluation [:result :status])
   :reason (get-in evaluation [:result :reason])
   :states-created (get-in evaluation [:result :telemetry :states-created])
   :reuse-successes (get-in evaluation [:result :telemetry :reuse-successes])})

(defn report [catalog-path build value replay]
  (let [mappings (:new-mappings build)
        mapped-names (set (map :foreign/name mappings))
        summary (mathlib/summarize catalog-path
                                   (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build)
                                        (:mappings value))
        definition-ids (vals (finite-type/definition-ids (:environment build)))
        theorem-ids (vals (:support-ids build))
        support-profiles
        (frequencies (map #(kernel/axioms (:environment build) %) theorem-ids))
        statuses (frequencies (map #(get-in % [:result :status])
                                   (:evaluations build)))
        validation-statuses
        (frequencies (map #(get-in % [:result :status])
                          (:validation-evaluations build)))
        all-proved (into (:proved build) (:validation-proved build))
        expected-profiles {#{} 3 #{(:excluded-middle-id build)} 2}
        passed?
        (and (= :replayed (:status replay))
             (= 7 (count (:targets build)))
             (= expected-gains mapped-names)
             (= 5 (count mappings))
             (= 4 (get statuses :proved 0))
             (= 1 (count (:validation-proved build)))
             (= 5 (accounting/new-proof-objects mappings))
             (= {#{} 3 #{(:excluded-middle-id build)} 2}
                (frequencies (map :axioms mappings)))
             (= expected-profiles support-profiles)
             (every? #(= 1 (get-in % [:result :telemetry :reuse-successes]))
                     all-proved)
             (every? #(= 2 (get-in % [:result :telemetry :states-created]))
                     all-proved)
             (every? #(checked? (:environment build) %)
                     (concat definition-ids theorem-ids
                             (map :native/id mappings)))
             (= 2 (count (:validation-targets build)))
             (= {:blocked 1 :proved 1} validation-statuses)
             (= 1180 (:proved summary))
             (= 77 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :proof-values :redacted
                  :catalog/id (get-in build [:batch :catalog/id])
                  :statement-batch/id (get-in build [:batch :batch/id])
                  :validation-batch/id
                  (get-in build [:validation-batch :batch/id])
                  :curriculum/id
                  (get-in build [:curriculum :or.curriculum/id])}
         :representation
         {:method :finite-carrier-as-list-cover
          :definitions (finite-type/definition-ids (:environment build))
          :definitions-counted-as-proofs? false
          :newly-nativeized (count (:targets build))
          :kernel-rechecked? true :trusted-kernel-change :none}
         :lemma-invention
         {:method :universal-set-finiteness-bridges
          :theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true}
         :experiment
         {:targets (count (:targets build)) :statuses statuses
          :evaluations (mapv compact-evaluation (:evaluations build))
          :validation
          {:partitions #{:held-out :transfer}
           :newly-nativeized (count (:validation-targets build))
           :statuses validation-statuses
           :evaluations
           (mapv compact-evaluation (:validation-evaluations build))
           :representation-promoted-globally? true}}
         :proofs {:new-foreign-mappings (count mappings)
                  :new-semantic-proof-objects
                  (accounting/new-proof-objects mappings)
                  :new-axiom-profiles (frequencies (map :axioms mappings))
                  :mappings mappings}
         :checkpoint {:id (:rainbow.checkpoint/id value)
                      :kernel-replay (:status replay)
                      :mappings (count (:mappings value))}
         :coverage {:exact-statement-mappings (:proved summary)
                    :theorem-declarations (:theorems summary)
                    :percent (* 100 (get-in summary [:coverage :ratio]))
                    :or-selected-exact-mappings
                    (:exact-selected-mappings or-coverage)
                    :or-selected-targets (:selected-targets or-coverage)}
         :claim-boundaries
         {:development-only-proof-gain? false
          :validation-proof-gain 1
          :support-theorems-counted-as-foreign-proofs? false
          :foreign-proof-values-present? false
          :new-proof-terms-kernel-rechecked? true
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
        {:status :rejected :error/category :day76/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day76/report-read-failed
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
