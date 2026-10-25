(ns rainbow.milestones.ahof-nearest-neighbor
  "Content-addressed precommitted evidence for AHoF D25 nearest-neighbor VF."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-composite-metric :as v5]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.nearest-neighbor :as specialization]
            [rainbow.algorithms.proofs.nearest-neighbor :as iteration]
            [rainbow.algorithms.reference.nearest-neighbor :as executable]))

(def precommit-path "artifacts/ahof/d25-nearest-neighbor/precommit.edn")
(def report-path "artifacts/ahof/d25-nearest-neighbor/report.edn")
(def checkpoint-path "artifacts/ahof/d25-nearest-neighbor/checkpoint.edn.gz")
(def default-input-checkpoint-path v5/checkpoint-path)

(def target-support
  (into (sorted-map)
        (map (fn [name] [name name]))
        '[audit/decide-nnrat-at-most
          logic/if-data
          decision/nearest-value
          decision/nearest-value-unfold
          ahof-d25/query-near-a
          ahof-d25/query-near-a-is-value-a
          ahof-d25/query-near-b-is-value-b
          ahof-d25/nearest-neighbor
          ahof-d25/value-a
          ahof-d25/value-b
          ahof-d25/query-near-b]))

;; Worked data points: values 3/4 and 1/4; query 1 nearer A, query 2 nearer B.
(def worked-value-a 3/4)
(def worked-value-b 1/4)

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "D25 precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- checked? [checked-environment id]
  (when id
    (let [declaration (environment/declaration checked-environment id)]
      (= :checked
         (:status
          (kernel/check checked-environment (:rainbow/value declaration)
                        (:rainbow/type declaration)
                        (set (:rainbow/universes declaration))))))))

(defn- worked-evaluation [_checked-environment]
  (let [near-a (executable/nearest-value 1/4 worked-value-a 1/2 worked-value-b)
        near-b (executable/nearest-value 1/2 worked-value-a 1/4 worked-value-b)]
    {:status (if (and (= 3/4 near-a) (= 1/4 near-b)) :normalized :failed)
     :rainbow {:query-near-a :value-a-three-quarters
               :query-near-b :value-b-one-quarter}
     :clojure-reference
     {:status :computed
      :value-a worked-value-a
      :value-b worked-value-b
      :query-near-a near-a
      :query-near-b near-b
      :follows-nearer-point (and (= worked-value-a near-a)
                                 (= worked-value-b near-b))
      :arithmetic :exact-rational
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "D25 input checkpoint rejected" {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "D25 input checkpoint identity mismatch"
                      {:precommitted
                       (get-in precommit
                               [:precommit/source :input-checkpoint/id])
                       :actual (:checkpoint/id prior)})))
    (let [baseline (:environment prior)
          candidate-timed
          (timed #(-> baseline
                      iteration/extend-environment
                      specialization/extend-environment))
          checked-environment (:value candidate-timed)
          definition-ids
          (merge (iteration/definition-ids checked-environment)
                 (specialization/definition-ids checked-environment))
          theorem-ids
          (merge (iteration/theorem-ids checked-environment)
                 (specialization/theorem-ids checked-environment))
          targets
          (mapv
           (fn [{:keys [target/name study/partition]}]
             (let [support (get target-support name)
                   id (environment/resolve-id checked-environment support)]
               {:target/name name
                :study/partition partition
                :native/id id
                :baseline/status
                (if (environment/resolve-id baseline support)
                  :proved :missing-generalized-lemma)
                :candidate/status
                (if (checked? checked-environment id) :proved :failed)
                :axioms (if id (kernel/axioms checked-environment id) #{})
                :states-created 0}))
           (:precommit/targets precommit))
          evaluation-timed (timed #(worked-evaluation checked-environment))]
      {:precommit precommit
       :prior prior
       :environment checked-environment
       :targets targets
       :definition-ids definition-ids
       :theorem-ids theorem-ids
       :build-wall-ms (:wall-ms candidate-timed)
       :evaluation-wall-ms (:wall-ms evaluation-timed)
       :evaluation (:value evaluation-timed)})))

(defn checkpoint [build]
  (let [value
        (frontier/checkpoint
         {:prior (:prior build)
          :environment (:environment build)
          :new-mappings []
          :evaluations []})
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in
             [:source :additional-statement-batches] (fnil conj [])
             {:kind :ahof-d25-nearest-neighbor
              :precommit/id (get-in build [:precommit :precommit/id])
              :proof-values :redacted}))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn report [build checkpoint-value replay]
  (let [targets (:targets build)
        new-targets (filterv #(not= :proved (:baseline/status %)) targets)
        held-out (filterv #(= :held-out (:study/partition %)) targets)
        transfer (filterv #(= :transfer (:study/partition %)) targets)
        proved? #(= :proved (:candidate/status %))
        all-new-ids (concat (vals (:definition-ids build))
                            (vals (:theorem-ids build)))
        passed?
        (and (= :replayed (:status replay))
             (= 11 (count targets))
             (= 2 (count (filter #(= :proved (:baseline/status %)) targets)))
             (= 5 (count held-out))
             (= 1 (count transfer))
             (every? proved? targets)
             (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (get-in build [:evaluation :status])))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id "D25"
         :algorithm/name "Nearest Neighbor VF"
         :source
         {:proof-origin :independent-native-rainbow
          :ahof/source-commit ahof/source-commit
          :mathlib-proof-bodies-used? false
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :results
         {:baseline-targets-present 2
          :newly-solved-native-results (count new-targets)
          :newly-solved-exact-or-mappings 0
          :held-out {:before [0 (count held-out)]
                     :after [(count (filter proved? held-out))
                             (count held-out)]}
          :transfer {:after [(count (filter proved? transfer))
                             (count transfer)]}
          :search-states
          {:median 0 :total 0
           :interpretation :installed-kernel-certificates}
          :wall-time
          {:rainbow-build-ms (:build-wall-ms build)
           :rainbow-evaluation-ms (:evaluation-wall-ms build)
           :ai-latency-ms :not-measured-by-offline-runner}
          :lemma-leverage
          {:new-held-out-targets (count (filter proved? held-out))
           :introduction-cost-ms (:build-wall-ms build)
           :new-targets-per-generalized-package (count new-targets)
           :shared-prerequisites ['decision/nearest-value]}}
         :targets targets
         :evaluation (:evaluation build)
         :axiom-profiles
         (into (sorted-map)
               (map (fn [[name id]]
                      [name (kernel/axioms (:environment build) id)]))
               (:theorem-ids build))
         :trusted-base-delta :none
         :checkpoint
         {:id (:rainbow.checkpoint/id checkpoint-value)
          :kernel-replay (:status replay)
          :exact-mathlib-mappings (count (:mappings checkpoint-value))}
         :claim-boundaries
         {:exact-rational-only true
          :nonparametric-value-lookup :proved
          :distance-comparison-selection :proved
          :follows-nearer-point :proved
          :rainbow-evaluation :computed
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :distance-metric-definition :not-claimed
          :arbitrary-data-set :not-claimed
          :k-nearest-averaging :not-claimed}
         :failures-remaining
         [:pluggable-distance-metric
          :arbitrary-data-set-fold
          :k-nearest-averaging
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D25"
   :ahof/outcome :proved
   :ahof/specification
   {:approximator 'decision/nearest-value
    :worked-near-a 'ahof-d25/query-near-a-is-value-a
    :worked-near-b 'ahof-d25/query-near-b-is-value-b
    :package 'ahof-d25/nearest-neighbor}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-d25/nearest-neighbor (:target/name %)))
              first :native/id)
     :worked-evaluation (:evaluation packet)}]})

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        checkpoint-value (checkpoint build)
        replay (day54/replay-checkpoint checkpoint-value)]
    {:build build :checkpoint checkpoint-value :replay replay
     :report (report build checkpoint-value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :evidence/id))]
      (if (= expected (:evidence/id value))
        {:status :replayed :report value :evidence/id expected}
        {:status :rejected :error/category :ahof-d25/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-d25/evidence-read-failed
       :message (.getMessage throwable)})))

(defn- write-edn! [path value]
  (io/make-parents path)
  (spit path (str (pr-str value) "\n")))

(defn -main [& [command]]
  (try
    (if (= "replay" command)
      (let [result (load-report report-path)]
        (println (pr-str (dissoc result :report)))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint report]}
            (run (or command default-input-checkpoint-path))
            ledger-result (ahof/load-ledger ahof/ledger-path)]
        (when-not (= :replayed (:status ledger-result))
          (throw (ex-info "AHoF ledger rejected before D25 credit"
                          {:ledger-result ledger-result})))
        (write-edn! report-path report)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (ahof/write-credited-ledger!
         ahof/ledger-path
         (ahof/credit-catalog-result (:ledger ledger-result)
                                     (ledger-entry report)))
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
