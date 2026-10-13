(ns rainbow.milestones.nat-distance
  "Equal-budget evidence for the precommitted Mathlib Nat-distance batch."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.accounting :as accounting]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.milestones.finite-nat :as finite-nat]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.distance :as nat-distance]
            [rainbow.math.nat.linear-order :as nat-linear-order]
            [rainbow.math.nat.metric :as nat-metric]
            [rainbow.math.nat.order :as nat-order]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def precommit-path "artifacts/nat-order-mathlib/precommit.edn")
(def statement-path "artifacts/nat-order-mathlib/statements.edn")
(def report-path "artifacts/nat-order-mathlib/report.edn")
(def checkpoint-path "artifacts/nat-order-mathlib/checkpoint.edn.gz")
(def default-input-checkpoint-path finite-nat/checkpoint-path)
(def default-catalog-path finite-nat/default-catalog-path)

(def target-support
  {"Nat.dist_comm" 'nat/distance-commutative
   "Nat.dist_succ_succ" 'nat/distance-successor
   "Nat.dist_add_add_left" 'nat/distance-add-left
   "Nat.dist_add_add_right" 'nat/distance-add-right
   "Nat.dist.triangle_inequality" 'nat/distance-triangle
   "Nat.dist_tri_left" 'nat/distance-left-bound
   "Nat.dist_tri_right" 'nat/distance-right-bound})

(def smallest-missing-prerequisite
  {"Nat.instLinearOrder._proof_1" :computational-nat-min-and-decidable-at-most
   "Nat.instLinearOrder._proof_2" :computational-nat-max-and-decidable-at-most
   "Nat.instLinearOrder._proof_3" :computational-three-way-nat-comparison
   "Nat.dist.triangle_inequality" :general-distance-triangle-inequality
   "Nat.dist_tri_left" :distance-left-bound
   "Nat.dist_tri_right" :distance-right-bound})

(def baseline-aliases
  (merge finite-sets/constant-aliases finset-range/constant-aliases))

(def candidate-aliases
  (merge baseline-aliases nat-distance/constant-aliases
         nat-linear-order/constant-aliases))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Nat-distance precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- nativeize [checked-environment aliases statements]
  (mapv #(ingest/nativeize-statement checked-environment % aliases)
        statements))

(defn- prove [checked-environment target options]
  (search/prove
   (:state (proof/start checked-environment (:type target)
                        {:universes (:universes target)}))
   options))

(defn build [input-checkpoint-path catalog-path]
  (let [precommit (load-precommit)
        names (mapv :foreign/name (:precommit/targets precommit))
        partitions (into {} (map (juxt :foreign/name :study/partition))
                         (:precommit/targets precommit))
        prior (checkpoint/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "Nat-distance input checkpoint rejected" {:prior prior})))
    (let [batch (mathlib/verify-statement-batch catalog-path statement-path names)
          _ (when-not (= (get-in precommit
                                 [:precommit/source :statement-batch/id])
                         (:batch/id batch))
              (throw (ex-info "Nat-distance batch changed after precommit"
                              {:expected (get-in precommit
                                                 [:precommit/source
                                                  :statement-batch/id])
                               :actual (:batch/id batch)})))
          baseline-timed
          (timed #(nativeize (:environment prior) baseline-aliases
                             (:statements batch)))
          support-environment
          (-> (:environment prior)
              finite-expectation/extend-environment
              nat-order/extend-environment
              nat-distance/extend-environment
              nat-metric/extend-environment
              nat-linear-order/extend-environment)
          definition-ids (nat-distance/definition-ids support-environment)
          linear-order-definition-ids
          (nat-linear-order/definition-ids support-environment)
          ordering-block-id (nat-linear-order/block-id support-environment)
          order-theorem-ids (nat-order/theorem-ids support-environment)
          theorem-ids (merge (nat-distance/theorem-ids support-environment)
                             (nat-metric/theorem-ids support-environment))
          reuse-ids (mapv theorem-ids (vals target-support))
          reuse-index (reuse/build-index support-environment
                                         {:include-ids reuse-ids})
          options (assoc preset-wide/candidate-options
                         :states 32 :depth 64
                         :reuse-index reuse-index
                         :reuse-policy {:allowed-axioms #{}})
          candidate-nativeization
          (timed #(nativeize support-environment candidate-aliases
                             (:statements batch)))
          evaluations-timed
          (timed
           #(mapv
             (fn [target]
               {:target target
                :study/partition (get partitions (:foreign/name target))
                :result (when (= :nativeized (:status target))
                          (prove support-environment target options))})
             (:value candidate-nativeization)))
          evaluations (:value evaluations-timed)
          proved (filterv #(= :proved (get-in % [:result :status])) evaluations)
          [checked-environment mappings]
          (reduce
           (fn [[current accepted] evaluation]
             (let [[next-environment mapping]
                   (ingest/add-result current evaluation
                                     :constructive-nat-distance
                                     "nat-distance-")]
               [next-environment (conj accepted mapping)]))
           [support-environment []] proved)]
      {:precommit precommit :prior prior :batch batch :partitions partitions
       :baseline-targets (:value baseline-timed)
       :baseline-nativeization-wall-ms (:wall-ms baseline-timed)
       :candidate-nativeization-wall-ms (:wall-ms candidate-nativeization)
       :candidate-search-wall-ms (:wall-ms evaluations-timed)
       :support-environment support-environment
       :definition-ids definition-ids :theorem-ids theorem-ids
       :linear-order-definition-ids linear-order-definition-ids
       :ordering-block-id ordering-block-id
       :order-theorem-ids order-theorem-ids
       :reuse-index reuse-index :options options :evaluations evaluations
       :proved proved :environment checked-environment
       :new-mappings mappings})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint build)
        extra-source
        {:kind :constructive-nat-distance
         :precommit/id (get-in build [:precommit :precommit/id])
         :statement-batch/id (get-in build [:batch :batch/id])
         :target-names (set (map :foreign/name
                                (get-in build [:precommit
                                               :precommit/targets])))
         :proof-values :redacted}
        base (-> value
                 (dissoc :rainbow.checkpoint/id)
                 (update-in [:source :additional-statement-batches]
                            (fnil conj []) extra-source))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- compact-evaluation [baseline evaluation]
  (let [target (:target evaluation)
        name (:foreign/name target)
        result (:result evaluation)]
    {:foreign/name name
     :study/partition (:study/partition evaluation)
     :baseline/nativeization-status (:status baseline)
     :baseline/error-category (get-in baseline [:error :error/category])
     :candidate/nativeization-status (:status target)
     :candidate/error-category (get-in target [:error :error/category])
     :candidate/status (or (:status result) :not-run)
     :candidate/reason (:reason result)
     :candidate/states-created (get-in result [:telemetry :states-created] 0)
     :candidate/wall-ms (get-in result [:telemetry :wall-ms] 0)
     :candidate/reuse-successes
     (get-in result [:telemetry :reuse-successes] 0)
     :smallest-missing-prerequisite
     (when-not (= :proved (:status result))
       (get smallest-missing-prerequisite name))}))

(defn- median [numbers]
  (when (seq numbers)
    (let [ordered (vec (sort numbers))]
      (nth ordered (quot (count ordered) 2)))))

(defn report [catalog-path build value replay]
  (let [evaluations
        (mapv compact-evaluation (:baseline-targets build) (:evaluations build))
        proved-evaluations (filterv #(= :proved (:candidate/status %))
                                    evaluations)
        proved-names (set (map :foreign/name proved-evaluations))
        expected-proved
        (set (map :foreign/name
                  (get-in build [:precommit :precommit/targets])))
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        held-out-proved (count (filter #(= :proved (:candidate/status %))
                                      held-out))
        transfer-proved (count (filter #(= :proved (:candidate/status %))
                                      transfer))
        states (mapv :candidate/states-created proved-evaluations)
        all-support-ids (concat (vals (:definition-ids build))
                                (vals (:linear-order-definition-ids build))
                                (vals (:theorem-ids build))
                                (vals (:order-theorem-ids build)))
        support-profiles
        (into (sorted-map)
              (map (fn [[name id]]
                     [name (kernel/axioms (:environment build) id)]))
              (:theorem-ids build))
        summary (mathlib/summarize
                 catalog-path (set (map :foreign/name (:mappings value))))
        passed?
        (and (= :replayed (:status replay))
             (= :verified (get-in build [:batch :status]))
             (= 10 (count evaluations))
             (zero? (count (filter #(= :nativeized
                                        (:baseline/nativeization-status %))
                                   evaluations)))
             (= expected-proved proved-names)
             (= 10 (count (:new-mappings build)))
             (= 2 held-out-proved)
             (= 2 transfer-proved)
             (every? empty? (vals support-profiles))
             (every? #(checked? (:environment build) %) all-support-ids)
             (every? #(checked? (:environment build) %)
                     (map :native/id (:new-mappings build))))
        base
        {:status (if passed? :passed :failed)
         :source
         {:library :mathlib :version mathlib/pinned-version
          :commit mathlib/pinned-commit :proof-values :redacted
          :catalog/id (get-in build [:batch :catalog/id])
          :statement-batch/id (get-in build [:batch :batch/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :capability
         {:kind :constructive-computational-nat-order-metric
          :definitions (:definition-ids build)
          :linear-order-definitions (:linear-order-definition-ids build)
          :ordering-block/id (:ordering-block-id build)
          :generalized-theorems (:theorem-ids build)
          :order-dependencies (:order-theorem-ids build)
          :axiom-profiles support-profiles
          :kernel-rechecked? true
          :trusted-base-delta :none}
         :equal-resource-experiment
         {:state-budget 32 :depth-budget 64
          :targets (count evaluations)
          :baseline-nativeizable
          (count (filter #(= :nativeized
                             (:baseline/nativeization-status %)) evaluations))
          :candidate-nativeizable
          (count (filter #(= :nativeized
                             (:candidate/nativeization-status %)) evaluations))
          :candidate-proved (count proved-evaluations)
          :baseline-rainbow-compute-ms
          (:baseline-nativeization-wall-ms build)
          :candidate-nativeization-compute-ms
          (:candidate-nativeization-wall-ms build)
          :candidate-search-compute-ms (:candidate-search-wall-ms build)
          :ai-latency-ms :not-instrumented
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
          {:new-generalized-lemmas (count (:theorem-ids build))
           :newly-solved-held-out-targets held-out-proved
           :held-out-targets-per-lemma
           (/ held-out-proved (count (:theorem-ids build)))
           :all-targets-per-lemma
           (/ (count proved-evaluations) (count (:theorem-ids build)))
           :ai-inclusive-cost :not-instrumented}
          :representation-leverage
          {:new-linear-order-definitions
           (count (:linear-order-definition-ids build))
           :newly-nativeized-linear-order-targets 3
           :targets-per-definition
           (/ 3 (count (:linear-order-definition-ids build)))}
          :evaluations evaluations
          :remaining-failures
          (filterv #(not= :proved (:candidate/status %)) evaluations)}
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
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))}
         :claim-boundaries
         {:proof-redacted-evaluation? true
          :support-theorems-counted-as-foreign-proofs? false
          :triangle-inequality-proved? true
          :linear-order-representation-complete? true
          :trusted-kernel-change :none}}
        value (assoc base :report/id (canonical/content-id base))]
    value))

(defn run [input-checkpoint-path catalog-path]
  (let [build (build input-checkpoint-path catalog-path)
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
        {:status :rejected :error/category :nat-distance/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :nat-distance/report-read-failed
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
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path)
                 (or catalog-path default-catalog-path))]
        (write-report! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
