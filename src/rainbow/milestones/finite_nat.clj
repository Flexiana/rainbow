(ns rainbow.milestones.finite-nat
  "Precommitted equal-budget evaluation of native finite-Nat capability."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.accounting :as accounting]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.subtype :as finite-subtype]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.finset :as finset]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.filter :as finset-filter]
            [rainbow.math.sets.finset.nontrivial :as finset-nontrivial]
            [rainbow.math.sets.finset.powerset :as finset-powerset]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.logic.fintype :as fintype]
            [rainbow.math.logic.infinite-transport :as infinite-transport]
            [rainbow.math.sets.range :as set-range]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/finite-nat-milestone/report.edn")
(def checkpoint-path "artifacts/finite-nat-milestone/checkpoint.edn.gz")
(def precommit-path "artifacts/finite-nat-milestone/precommit.edn")
(def statement-path "artifacts/finite-nat-milestone/statements.edn")
(def default-input-checkpoint-path preset-late/checkpoint-path)
(def default-catalog-path preset-late/default-catalog-path)
(def default-curriculum-path preset-late/default-curriculum-path)

(def target-support
  {"Finset.card_range" 'finset-data/card-range
   "Finset.exists_nat_subset_range" 'finset/exists-nat-subset-range
   "Finset.filter_false" 'finset/filter-false
   "Finset.mem_range._simp_1" 'finset/member-range-proposition-equality
   "Finset.notMem_range_self" 'finset/not-member-range-self
   "Finset.range_mono" 'finset/range-monotone
   "Finset.range_subset_range" 'finset/range-subset-equivalent-at-most
   "Finset.range_subset_range._gcongr_1"
   'finset/range-subset-of-at-most})

(def prior-aliases
  (merge finite-sets/constant-aliases
         finite-type/constant-aliases
         finite-subtype/constant-aliases
         infinite-transport/constant-aliases
         finset/constant-aliases
         finset-nontrivial/constant-aliases
         finset-powerset/constant-aliases
         fintype/constant-aliases
         set-range/constant-aliases))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Finite-Nat precommit identity mismatch"
                      {:error/category :finite-nat/precommit-id
                       :expected expected :actual (:precommit/id value)})))
    value))

(defn- nativeize [checked-environment aliases statements]
  (mapv #(ingest/nativeize-statement checked-environment % aliases)
        statements))

(defn- candidate-nativeize
  "Use the computational Finset representation only when an operation requires
  eliminable finite data. Other targets retain the extensional representation."
  [checked-environment aliases statements]
  (mapv
   (fn [statement]
     (ingest/nativeize-statement
      checked-environment statement
      (if (contains? (mathlib/statement-constant-names statement)
                     "Finset.card")
        (merge aliases finset-data/constant-aliases)
        aliases)))
   statements))

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn build [input-checkpoint-path catalog-path curriculum-path]
  (let [precommit (load-precommit)
        names (mapv :foreign/name (:precommit/targets precommit))
        partitions (into {} (map (juxt :foreign/name :study/partition))
                         (:precommit/targets precommit))
        prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Finite-Nat input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          batch (mathlib/verify-statement-batch catalog-path statement-path names)
          _ (when-not (= (get-in precommit [:precommit/source
                                            :statement-batch/id])
                         (:batch/id batch))
              (throw (ex-info "Finite-Nat statement batch changed after precommit"
                              {:error/category :finite-nat/batch-changed})))
          baseline-timed
          (timed #(nativeize (:environment prior) prior-aliases
                             (:statements batch)))
          baseline-targets (:value baseline-timed)
          support-environment
          (-> (:environment prior)
              finset-range/extend-environment
              finset-filter/extend-environment
              finset-data/extend-environment)
          aliases (merge prior-aliases
                         finset-range/constant-aliases
                         finset-filter/constant-aliases)
          range-definition-ids (finset-range/definition-ids support-environment)
          filter-definition-ids (finset-filter/definition-ids support-environment)
          data-definition-ids (finset-data/definition-ids support-environment)
          definition-ids (merge range-definition-ids filter-definition-ids
                                data-definition-ids)
          range-theorem-ids (finset-range/theorem-ids support-environment)
          filter-theorem-ids (finset-filter/theorem-ids support-environment)
          data-theorem-ids (finset-data/theorem-ids support-environment)
          support-ids (merge range-theorem-ids filter-theorem-ids
                             data-theorem-ids)
          reuse-ids (mapv #(get support-ids %) (vals target-support))
          reuse-index (reuse/build-index support-environment
                                         {:include-ids reuse-ids})
          allowed-axioms
          (set (map #(environment/resolve-id support-environment %)
                    ['logic/proof-irrelevance
                     'logic/function-extensionality
                     'logic/proposition-extensionality]))
          options (assoc preset-wide/candidate-options :reuse-index reuse-index
                         :reuse-policy {:allowed-axioms allowed-axioms})
          candidate-timed
          (timed
           #(let [targets (candidate-nativeize support-environment aliases
                                               (:statements batch))]
              (mapv
               (fn [target]
                 {:target target
                  :study/partition (get partitions (:foreign/name target))
                  :result (when (= :nativeized (:status target))
                            (prove support-environment target options))})
               targets)))
          evaluations (:value candidate-timed)
          proved (filterv #(= :proved (get-in % [:result :status]))
                          evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :finite-nat-capability
                                     "finite-nat-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)]
      {:precommit precommit :prior prior :curriculum curriculum :batch batch
       :partitions partitions :baseline-targets baseline-targets
       :baseline-wall-ms (:wall-ms baseline-timed)
       :support-environment support-environment :aliases aliases
       :definition-ids definition-ids :support-ids support-ids
       :reuse-index reuse-index :allowed-axioms allowed-axioms :options options
       :evaluations evaluations :candidate-wall-ms (:wall-ms candidate-timed)
       :proved proved :environment checked-environment
       :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :finite-nat-capability
         :precommit/id (get-in build [:precommit :precommit/id])
         :statement-batch/id (get-in build [:batch :batch/id])
         :target-names (set (map :foreign/name
                                (get-in build [:precommit
                                               :precommit/targets])))
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

(defn- compact-evaluation [baseline evaluation]
  (let [result (:result evaluation)]
    {:foreign/name (get-in evaluation [:target :foreign/name])
     :study/partition (:study/partition evaluation)
     :baseline/nativeization-status (:status baseline)
     :baseline/error-category (get-in baseline [:error :error/category])
     :candidate/nativeization-status (get-in evaluation [:target :status])
     :candidate/error-category (get-in evaluation [:target :error :error/category])
     :candidate/status (or (:status result) :not-run)
     :candidate/reason (:reason result)
     :candidate/states-created (get-in result [:telemetry :states-created] 0)
     :candidate/wall-ms (get-in result [:telemetry :wall-ms] 0)
     :candidate/reuse-successes (get-in result [:telemetry :reuse-successes] 0)}))

(defn- median [numbers]
  (when (seq numbers)
    (let [ordered (vec (sort numbers))]
      (nth ordered (quot (count ordered) 2)))))

(defn report [catalog-path build value replay]
  (let [mappings (:new-mappings build)
        mapped-names (set (map :foreign/name mappings))
        expected-mapped (set (keys target-support))
        proof-ids (set (map :proof/id mappings))
        evaluations
        (mapv compact-evaluation (:baseline-targets build) (:evaluations build))
        proved-evaluations (filterv #(= :proved (:candidate/status %)) evaluations)
        states (mapv :candidate/states-created proved-evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-out-proved (count (filter #(= :proved (:candidate/status %)) held-out))
        transfer-proved (count (filter #(= :proved (:candidate/status %)) transfer))
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
             (= expected-mapped mapped-names)
             (= 8 (count mappings) (count proof-ids))
             (= 8 (count evaluations))
             (every? #(= :rejected (:baseline/nativeization-status %)) evaluations)
             (= 8 (count proved-evaluations))
             (= 2 held-out-proved transfer-proved)
             (every? #(= 2 (:candidate/states-created %)) proved-evaluations)
             (every? #(= 1 (:candidate/reuse-successes %)) proved-evaluations)
             (every? #(checked? (:environment build) %) all-ids)
             (= 1227 (:proved summary))
             (= 124 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:batch :catalog/id])
          :statement-batch/id (get-in build [:batch :batch/id])
          :precommit/id (get-in build [:precommit :precommit/id])
          :curriculum/id (get-in build [:curriculum :or.curriculum/id])}
         :capability
         {:kind :computational-finite-nat-data
          :definitions (:definition-ids build)
          :generalized-theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget (:states preset-wide/candidate-options)
          :depth-budget (:depth preset-wide/candidate-options)
          :baseline-nativeizable 0
          :candidate-nativeizable 8
          :baseline-rainbow-compute-ms (:baseline-wall-ms build)
          :candidate-rainbow-compute-ms (:candidate-wall-ms build)
          :ai-latency-ms :not-instrumented
          :evaluations evaluations
          :search-cost
          {:proved-targets (count proved-evaluations)
           :median-states (median states)
           :total-states (reduce + states)
           :total-search-wall-ms
           (reduce + (map :candidate/wall-ms proved-evaluations))}
          :held-out
          {:baseline-successes 0 :targets (count held-out)
           :candidate-successes held-out-proved
           :success-rate-change (/ held-out-proved (count held-out))}
          :transfer
          {:baseline-successes 0 :targets (count transfer)
           :candidate-successes transfer-proved}
          :lemma-leverage
          {:new-generalized-lemmas (count (:support-ids build))
           :newly-solved-held-out-targets held-out-proved
           :held-out-targets-per-lemma
           (/ held-out-proved (count (:support-ids build)))
           :all-targets-per-lemma
           (/ (count proved-evaluations) (count (:support-ids build)))
           :ai-inclusive-cost :not-instrumented}
          :remaining-failures []}
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
          :or-selected-exact-mappings (:exact-selected-mappings or-coverage)
          :or-selected-targets (:selected-targets or-coverage)}
         :claim-boundaries
         {:support-theorems-counted-as-foreign-proofs? false
          :baseline-nativeization-failures-counted-as-search-failures? false
          :human-facing-capability-release-complete? false
          :canonical-cardinality-complete-for-computational-finset? true
          :extensional-finset-proposition-elimination-added? false
          :executable-or-chain-complete? false
          :foreign-proof-values-present? false
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path curriculum-path]
  (let [build (build input-checkpoint-path catalog-path curriculum-path)
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
        {:status :rejected :error/category :finite-nat/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :finite-nat/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command catalog-path curriculum-path]]
  (try
    (if (= "replay" command)
      (let [result (load-report (or catalog-path report-path))]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path)
                 (or catalog-path default-catalog-path)
                 (or curriculum-path default-curriculum-path))]
        (write-report! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
