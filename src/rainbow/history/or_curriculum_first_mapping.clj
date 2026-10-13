(ns rainbow.history.or-curriculum-first-mapping
  "First exact mapping from the operations-research foundation curriculum."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.accounting :as accounting]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.or-foundation :as foundation]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day75/report.edn")
(def checkpoint-path "artifacts/day75/checkpoint.edn.gz")
(def default-input-checkpoint-path preset-wide/checkpoint-path)
(def default-catalog-path preset-wide/default-catalog-path)
(def default-statement-path or40/default-statement-path)
(def default-curriculum-path or40/curriculum-path)
(def target-name "Finset.diag._proof_1")

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn build [input-checkpoint-path statement-path curriculum-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 75 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          selected (or40/next-proof-batch curriculum (:mappings prior))
          names (mapv :foreign/name selected)
          batch (mathlib/verify-statement-batch default-catalog-path
                                                statement-path names)
          statement (first (filter #(= target-name (:foreign/name %))
                                   (:statements batch)))
          _ (when-not statement
              (throw (ex-info "Day 75 target is absent from the OR batch"
                              {:error/category :day75/target-absent})))
          baseline-target
          (ingest/nativeize-statement (:environment prior) statement
                                     finite-sets/constant-aliases)
          _ (when-not (= :nativeized (:status baseline-target))
              (throw (ex-info "Day 75 baseline target did not nativeize"
                              {:target baseline-target})))
          baseline (prove (:environment prior) baseline-target
                          preset-wide/candidate-options)
          support-environment
          (foundation/extend-environment (:environment prior))
          target (ingest/nativeize-statement support-environment statement
                                            finite-sets/constant-aliases)
          support-ids (foundation/theorem-ids support-environment)
          reuse-index
          (reuse/build-index support-environment
                             {:include-ids (vals support-ids)})
          candidate
          (prove support-environment target
                 (assoc preset-wide/candidate-options :reuse-index reuse-index))
          evaluation {:target target :baseline baseline :result candidate
                      :study/partition
                      (:study/partition
                       (first (filter #(= target-name (:foreign/name %))
                                      selected)))}
          [checked-environment mapping]
          (if (= :proved (:status candidate))
            (ingest/add-result support-environment evaluation
                              :or-product-diagonal-reuse "or-diagonal-")
            [support-environment nil])]
      {:prior prior :curriculum curriculum :selected selected :batch batch
       :statement statement :baseline-target baseline-target
       :baseline baseline :support-environment support-environment
       :target target :support-ids support-ids :reuse-index reuse-index
       :candidate candidate :evaluation evaluation
       :evaluations [evaluation]
       :environment checked-environment
       :new-mappings (cond-> [] mapping (conj mapping))})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :operations-research-foundation
         :curriculum/id (get-in build [:curriculum :or.curriculum/id])
         :statement-batch/id (get-in build [:batch :batch/id])
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

(defn report [catalog-path build value replay]
  (let [mapping (first (:new-mappings build))
        support-id (get (:support-ids build)
                        'function/product-diagonal-injective)
        summary (mathlib/summarize
                 catalog-path (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build)
                                        (:mappings value))
        audit (or40/audit-next-batch default-statement-path
                                     (:curriculum build) (:prior build))
        passed?
        (and (= :replayed (:status replay))
             (= :blocked (get-in build [:baseline :status]))
             (= :frontier-exhausted (get-in build [:baseline :reason]))
             (= :proved (get-in build [:candidate :status]))
             (= 1 (get-in build [:candidate :telemetry :reuse-successes]))
             (= 2 (get-in build [:candidate :telemetry :states-created]))
             (= target-name (:foreign/name mapping))
             (empty? (:axioms mapping))
             (checked? (:environment build) support-id)
             (checked? (:environment build) (:native/id mapping))
             (= 4 (:kernel-nativeized audit))
             (= 1175 (:proved summary))
             (= 72 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :proof-values :redacted
                  :catalog/id (get-in build [:batch :catalog/id])
                  :statement-batch/id (get-in build [:batch :batch/id])
                  :curriculum/id
                  (get-in build [:curriculum :or.curriculum/id])}
         :foundation-batch
         (select-keys audit [:audit/id :targets :fully-nativeizable
                             :kernel-nativeized :nativeization-rejected
                             :single-blocker-statements
                             :top-unresolved-constants])
         :lemma-invention
         {:method :product-projection-injectivity
          :theorem 'function/product-diagonal-injective
          :native/id support-id :axioms (kernel/axioms (:environment build)
                                                       support-id)
          :kernel-rechecked? true :trusted-kernel-change :none}
         :experiment
         {:target target-name
          :partition (:study/partition (:evaluation build))
          :baseline {:status (get-in build [:baseline :status])
                     :reason (get-in build [:baseline :reason])
                     :states-created
                     (get-in build [:baseline :telemetry :states-created])}
          :candidate {:status (get-in build [:candidate :status])
                      :states-created
                      (get-in build [:candidate :telemetry :states-created])
                      :reuse-successes
                      (get-in build [:candidate :telemetry :reuse-successes])}}
         :proofs {:new-foreign-mappings (count (:new-mappings build))
                  :new-semantic-proof-objects
                  (accounting/new-proof-objects (:new-mappings build))
                  :mappings (:new-mappings build)}
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
         {:support-theorem-counted-as-foreign-proof? false
          :foreign-proof-values-present? false
          :new-proof-terms-kernel-rechecked? true
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn run [input-checkpoint-path catalog-path statement-path curriculum-path]
  (let [build (build input-checkpoint-path statement-path curriculum-path)
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
        {:status :rejected :error/category :day75/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day75/report-read-failed
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
