(ns rainbow.history.classical-infinitude-transport
  "Classical, sort-polymorphic infinitude transport along injections."
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
            [rainbow.history.infinitude-transport :as infinitude-transport]
            [rainbow.curriculum.operations-research :as or40]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.infinite-injection :as infinite-injection]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day80/report.edn")
(def checkpoint-path "artifacts/day80/checkpoint.edn.gz")
(def default-input-checkpoint-path infinitude-transport/checkpoint-path)
(def default-catalog-path or-curriculum-first-mapping/default-catalog-path)
(def default-curriculum-path or-curriculum-first-mapping/default-curriculum-path)
(def default-statement-path "artifacts/day80/injection-statement.edn")
(def target-name "Infinite.of_injective")

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn build [input-checkpoint-path catalog-path statement-path curriculum-path]
  (let [prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Day 80 input checkpoint was rejected" {:prior prior})))
    (let [curriculum (edn/read-string (slurp curriculum-path))
          partitions (into {} (map (juxt :foreign/name :study/partition))
                           (:or.curriculum/targets curriculum))
          batch (mathlib/verify-statement-batch catalog-path statement-path
                                                [target-name])
          statement (first (:statements batch))
          aliases (merge finite-sets/constant-aliases finite-type/constant-aliases)
          baseline-target
          (ingest/nativeize-statement (:environment prior) statement aliases)
          _ (when-not (= :nativeized (:status baseline-target))
              (throw (ex-info "Day 80 baseline target did not nativeize"
                              {:target baseline-target})))
          baseline (prove (:environment prior) baseline-target
                          preset-wide/candidate-options)
          support-environment
          (infinite-injection/extend-environment (:environment prior))
          target (ingest/nativeize-statement support-environment statement aliases)
          _ (when-not (= :nativeized (:status target))
              (throw (ex-info "Day 80 candidate target did not nativeize"
                              {:target target})))
          support-ids (infinite-injection/theorem-ids support-environment)
          reuse-id (get support-ids 'type/infinite-of-injection)
          reuse-index (reuse/build-index support-environment
                                         {:include-ids [reuse-id]})
          excluded-middle-id
          (environment/resolve-id support-environment 'logic/excluded-middle)
          allowed-axioms #{excluded-middle-id}
          candidate-options
          (assoc preset-wide/candidate-options :reuse-index reuse-index
                 :reuse-policy {:allowed-axioms allowed-axioms})
          candidate (prove support-environment target candidate-options)
          evaluation {:target target :baseline baseline :result candidate
                      :study/partition (get partitions target-name)}
          [checked-environment mapping]
          (if (= :proved (:status candidate))
            (ingest/add-result support-environment evaluation
                              :classical-infinite-injection
                              "infinite-injection-")
            [support-environment nil])]
      {:prior prior :curriculum curriculum :batch batch :statement statement
       :aliases aliases :baseline-target baseline-target :baseline baseline
       :support-environment support-environment :support-ids support-ids
       :excluded-middle-id excluded-middle-id :allowed-axioms allowed-axioms
       :target target :reuse-index reuse-index :candidate-options candidate-options
       :candidate candidate :evaluation evaluation :evaluations [evaluation]
       :environment checked-environment
       :new-mappings (cond-> [] mapping (conj mapping))})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :classical-infinite-injection
         :statement-batch/id (get-in build [:batch :batch/id])
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

(defn report [catalog-path build value replay]
  (let [mapping (first (:new-mappings build))
        summary (mathlib/summarize
                 catalog-path (set (map :foreign/name (:mappings value))))
        or-coverage (or40/audit-coverage (:curriculum build) (:mappings value))
        support-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:support-ids build))
        passed?
        (and (= :replayed (:status replay))
             (= :blocked (get-in build [:baseline :status]))
             (= :state-budget (get-in build [:baseline :reason]))
             (= 32 (get-in build [:baseline :telemetry :states-created]))
             (= :proved (get-in build [:candidate :status]))
             (= 1 (get-in build [:candidate :telemetry :reuse-successes]))
             (= 2 (get-in build [:candidate :telemetry :states-created]))
             (= target-name (:foreign/name mapping))
             (= (:allowed-axioms build) (:axioms mapping))
             (= #{:development} #{(:study/partition (:evaluation build))})
             (every? #(= (:allowed-axioms build) %)
                     (vals support-profiles))
             (every? #(checked? (:environment build) %)
                     (concat (vals (:support-ids build))
                             [(:native/id mapping)]))
             (= 1187 (:proved summary))
             (= 84 (:exact-selected-mappings or-coverage)))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:batch :catalog/id])
          :statement-batch/id (get-in build [:batch :batch/id])
          :curriculum/id (get-in build [:curriculum :or.curriculum/id])}
         :lemma-invention
         {:method :classical-preimage-representative-selection
          :theorems (:support-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true}
         :experiment
         {:target target-name
          :study/partition (:study/partition (:evaluation build))
          :state-budget (:states preset-wide/candidate-options)
          :baseline {:status (get-in build [:baseline :status])
                     :reason (get-in build [:baseline :reason])
                     :states-created
                     (get-in build [:baseline :telemetry :states-created])}
          :candidate {:status (get-in build [:candidate :status])
                      :states-created
                      (get-in build [:candidate :telemetry :states-created])
                      :reuse-successes
                      (get-in build [:candidate :telemetry :reuse-successes])}}
         :proofs
         {:new-foreign-mappings (count (:new-mappings build))
          :new-semantic-proof-objects
          (accounting/new-proof-objects (:new-mappings build))
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
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :or-selected-exact-mappings (:exact-selected-mappings or-coverage)
          :or-selected-targets (:selected-targets or-coverage)}
         :claim-boundaries
         {:development-only-proof-gain? true
          :support-theorems-counted-as-foreign-proofs? false
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
        {:status :rejected :error/category :day80/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day80/report-read-failed
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
