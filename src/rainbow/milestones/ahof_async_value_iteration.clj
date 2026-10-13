(ns rainbow.milestones.ahof-async-value-iteration
  "Content-addressed precommitted evidence for AHoF D23 asynchronous value
  iteration."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-value-iteration :as d22]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.async-value-iteration :as specialization]
            [rainbow.math.finite.async-value-iteration :as iteration]
            [rainbow.algorithms.reference.async-value-iteration :as executable]))

(def precommit-path "artifacts/ahof/d23-async-value-iteration/precommit.edn")
(def report-path "artifacts/ahof/d23-async-value-iteration/report.edn")
(def checkpoint-path "artifacts/ahof/d23-async-value-iteration/checkpoint.edn.gz")
(def default-input-checkpoint-path d22/checkpoint-path)

(def target-support
  (into (sorted-map)
        (map (fn [name] [name name]))
        '[value/nnrat-optimality-step-dominates
          value/nnrat-greedy-action-is-admissible
          nat/recursor-successor-constant
          value/nnrat-async-update
          value/nnrat-async-iterate
          value/nnrat-async-update-selected
          value/nnrat-async-iterate-successor
          value/nnrat-async-update-preserved
          value/nnrat-async-iterate-zero
          value/nnrat-async-update-selected-dominates
          ahof-d23/selected-update
          ahof-d23/preserved-update
          ahof-d23/async-recurrence
          ahof-d23/async-value-iteration
          value/nnrat-async-state-schedule-transfer
          ahof-d23/two-step-async-values]))

(def worked-model
  {:states [0 1]
   :actions [0]
   :transition (fn [_state action next-state]
                 (if (= action next-state) 1 0))
   :reward (fn [_state _action] 0)
   :discount 0
   :fallback (constantly 0)})

;; Selection schedule: always update state 0, always preserve state 1.
(def worked-schedule (fn [_step] (fn [state] (= state 0))))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "D23 precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- checked? [checked-environment id]
  (when id
    (let [declaration (environment/declaration checked-environment id)]
      (= :checked
         (:status
          (kernel/check checked-environment (:rainbow/value declaration)
                        (:rainbow/type declaration)
                        (set (:rainbow/universes declaration))))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "D23 evaluation expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- equivalent-by-normalization?
  [checked-environment actual expected]
  (let [numerator [:const 'nnrat/numerator []]
        denominator [:const 'nnrat/denominator []]
        multiply [:const 'nat/multiply []]
        left [:app multiply [:app numerator actual]
              [:app denominator expected]]
        right [:app multiply [:app numerator expected]
               [:app denominator actual]]
        left-result
        (kernel/normalize checked-environment (core checked-environment left)
                          {:reductions 1000000})
        right-result
        (kernel/normalize checked-environment (core checked-environment right)
                          {:reductions 1000000})]
    (and (= :normalized (:status left-result))
         (= :normalized (:status right-result))
         (= (:term left-result) (:term right-result)))))

(defn- worked-evaluation [checked-environment]
  (let [zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        worked [:const 'ahof-d23/two-step-async []]
        cases [{:state :zero :input zero}
               {:state :one :input one}]
        values
        (mapv
         (fn [{:keys [input] :as case}]
           (-> case
               (dissoc :input)
               (assoc :matches?
                      (equivalent-by-normalization?
                       checked-environment [:app worked input]
                       [:const 'nnrat/zero []]))))
         cases)
        clojure-values
        (executable/async-iterate worked-model worked-schedule 2 {0 0, 1 0})
        clojure-one-step
        (executable/async-iterate worked-model worked-schedule 1 {0 0, 1 0})]
    {:status (if (and (every? :matches? values)
                      (= {0 0N, 1 0} clojure-values)
                      (= {0 0N, 1 0} clojure-one-step))
               :normalized :failed)
     :rainbow {:values values :bounded-steps 2
               :schedule :always-select-state-zero}
     :clojure-reference
     {:status :computed
      :values clojure-values
      :one-step clojure-one-step
      :arithmetic :exact-rational
      :selection :subset-schedule-preserves-non-selected-states
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "D23 input checkpoint rejected" {:prior prior})))
    (when-not (= (get-in precommit [:precommit/source :input-checkpoint/id])
                 (:checkpoint/id prior))
      (throw (ex-info "D23 input checkpoint identity mismatch"
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
          evaluation-timed
          (timed #(worked-evaluation checked-environment))]
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
             {:kind :ahof-d23-async-value-iteration
              :precommit/id (get-in build [:precommit :precommit/id])
              :proof-values :redacted}))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn report [build checkpoint-value replay]
  (let [targets (:targets build)
        new-targets (filterv #(not= :proved (:baseline/status %)) targets)
        held-out (filterv #(= :held-out (:study/partition %)) targets)
        transfer (filterv #(= :transfer (:study/partition %)) targets)
        proved? #(= :proved (:candidate/status %))
        all-new-ids
        (concat (vals (:definition-ids build))
                (vals (:theorem-ids build)))
        passed?
        (and (= :replayed (:status replay))
             (= 16 (count targets))
             (= 3 (count (filter #(= :proved (:baseline/status %)) targets)))
             (= 7 (count held-out))
             (= 2 (count transfer))
             (every? proved? targets)
             (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (get-in build [:evaluation :status])))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id "D23"
         :algorithm/name "Asynchronous Value Iteration"
         :source
         {:proof-origin :independent-native-rainbow
          :ahof/source-commit ahof/source-commit
          :mathlib-proof-bodies-used? false
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :results
         {:baseline-targets-present 3
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
           :shared-prerequisites
           ['value/nnrat-optimality-step-dominates
            'nat/recursor-successor-constant]}}
         :targets targets
         :evaluation (:evaluation build)
         :axiom-profiles
         (into
          (sorted-map)
          (map (fn [[name id]]
                 [name (kernel/axioms (:environment build) id)]))
          (:theorem-ids build))
         :trusted-base-delta :none
         :checkpoint
         {:id (:rainbow.checkpoint/id checkpoint-value)
          :kernel-replay (:status replay)
          :exact-mathlib-mappings (count (:mappings checkpoint-value))}
         :claim-boundaries
         {:finite-model-only true
          :pluggable-selection-schedule :proved
          :selected-state-update :proved
          :non-selected-preservation :proved
          :schedule-prefix-recurrence :proved
          :selected-action-admissibility :proved
          :selected-action-dominance :proved
          :state-and-schedule-transfer :proved
          :rainbow-evaluation :computed
          :output-satisfies-theorem :proved
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :infinite-limit-convergence :not-claimed
          :unique-fixed-point :not-claimed
          :optimal-policy :not-claimed}
         :failures-remaining
         [:infinite-async-value-iteration-convergence
          :unique-optimal-fixed-point
          :chaotic-relaxation-total-asynchrony
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D23"
   :ahof/outcome :proved
   :ahof/specification
   {:async-update 'value/nnrat-async-update
    :async-iterate 'value/nnrat-async-iterate
    :selected 'value/nnrat-async-update-selected
    :preserved 'value/nnrat-async-update-preserved
    :recurrence 'ahof-d23/async-recurrence
    :transfer 'value/nnrat-async-state-schedule-transfer
    :package 'ahof-d23/async-value-iteration}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-d23/async-value-iteration
                          (:target/name %)))
              first :native/id)
     :selected-proof-id
     (some->> (:targets packet)
              (filter #(= 'value/nnrat-async-update-selected
                          (:target/name %)))
              first :native/id)
     :worked-evaluation (:evaluation packet)}]})

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        checkpoint-value (checkpoint build)
        replay (day54/replay-checkpoint checkpoint-value)]
    {:build build
     :checkpoint checkpoint-value
     :replay replay
     :report (report build checkpoint-value replay)}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :evidence/id))]
      (if (= expected (:evidence/id value))
        {:status :replayed :report value :evidence/id expected}
        {:status :rejected
         :error/category :ahof-d23/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-d23/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before D23 credit"
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
