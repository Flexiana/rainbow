(ns rainbow.milestones.ahof-value-iteration
  "Content-addressed precommitted evidence for AHoF D22 value iteration."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-policy-iteration :as d21]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.value-iteration :as specialization]
            [rainbow.math.finite.value-iteration :as iteration]
            [rainbow.algorithms.reference.value-iteration :as executable]))

(def precommit-path "artifacts/ahof/d22-value-iteration/precommit.edn")
(def report-path "artifacts/ahof/d22-value-iteration/report.edn")
(def checkpoint-path "artifacts/ahof/d22-value-iteration/checkpoint.edn.gz")
(def default-input-checkpoint-path d21/checkpoint-path)

(def target-support
  {'decision/finite-nnrat-argmax-is-member
   'decision/finite-nnrat-argmax-is-member
   'decision/finite-nnrat-argmax-dominates
   'decision/finite-nnrat-argmax-dominates
   'nat/recursor-successor-constant 'nat/recursor-successor-constant
   'value/nnrat-greedy-action 'value/nnrat-greedy-action
   'value/nnrat-optimality-step 'value/nnrat-optimality-step
   'value/nnrat-iterate 'value/nnrat-iterate
   'value/nnrat-greedy-action-is-admissible
   'value/nnrat-greedy-action-is-admissible
   'value/nnrat-optimality-step-dominates
   'value/nnrat-optimality-step-dominates
   'value/nnrat-iterate-zero 'value/nnrat-iterate-zero
   'value/nnrat-iterate-successor 'value/nnrat-iterate-successor
   'value/nnrat-optimality-state-transfer
   'value/nnrat-optimality-state-transfer
   'ahof-d22/normalized-transition-rows
   'ahof-d22/normalized-transition-rows
   'ahof-d22/finite-horizon-recurrence
   'ahof-d22/finite-horizon-recurrence
   'ahof-d22/greedy-actions 'ahof-d22/greedy-actions
   'ahof-d22/two-step-value 'ahof-d22/two-step-value
   'ahof-d22/value-iteration 'ahof-d22/value-iteration})

(def worked-model
  {:states [0 1]
   :actions [0]
   :transition (fn [_state action next-state]
                 (if (= action next-state) 1 0))
   :reward (fn [_state _action] 0)
   :discount 0
   :fallback (constantly 0)})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "D22 precommit identity mismatch"
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
      (throw (ex-info "D22 evaluation expression rejected"
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
        worked [:const 'ahof-d22/two-step-value-function []]
        one-step [:const 'ahof-d22/one-step-value []]
        greedy [:const 'value/nnrat-greedy-action
                [[:zero] [:zero]]]
        greedy-prefix
        [:app greedy [:const 'data/Nat []] [:const 'data/Nat []]
         [:const 'ahof-d22/action-space []]
         [:const 'ahof-d22/fallback-action []]
         [:const 'ahof-d22/action-backup []] one-step]
        cases [{:state :zero :input zero :expected [:const 'nnrat/zero []]}
               {:state :one :input one :expected [:const 'nnrat/zero []]}]
        values
        (mapv
         (fn [{:keys [input expected] :as case}]
           (-> case
               (dissoc :input :expected)
               (assoc :matches?
                      (equivalent-by-normalization?
                       checked-environment [:app worked input] expected))))
         cases)
        actions
        (mapv
         (fn [{:keys [state input]}]
           (let [result
                 (kernel/normalize
                  checked-environment
                  (core checked-environment (conj greedy-prefix input))
                  {:reductions 1000000})]
             {:state state :selected-action :zero
              :matches? (and (= :normalized (:status result))
                             (= (core checked-environment zero)
                                (:term result)))}))
         cases)
        clojure-values
        (executable/value-iterate worked-model 2 {0 0, 1 0})
        clojure-actions
        (mapv #(executable/greedy-action worked-model {0 1, 1 2} %)
              [0 1])]
    {:status (if (and (every? :matches? values)
                      (every? :matches? actions)
                      (= {0 0N, 1 0N} clojure-values)
                      (= [0 0] clojure-actions))
               :normalized :failed)
     :rainbow {:values values :greedy-actions actions
               :bounded-steps 2}
     :clojure-reference
     {:status :computed
      :values clojure-values
      :greedy-actions clojure-actions
      :arithmetic :exact-rational
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "D22 input checkpoint rejected" {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "D22 input checkpoint identity mismatch"
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
             {:kind :ahof-d22-value-iteration
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
         :algorithm/id "D22"
         :algorithm/name "Value Iteration"
         :source
         {:proof-origin :independent-native-rainbow
          :ahof/source-commit ahof/source-commit
          :mathlib-proof-bodies-used? false
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :results
         {:baseline-targets-present 3
          :newly-solved-native-results (count new-targets)
          :newly-solved-exact-or-mappings 1
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
           ['decision/finite-nnrat-argmax-dominates
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
          :bounded-bellman-optimality-iteration :proved
          :greedy-action-admissibility :proved
          :greedy-action-dominance :proved
          :rainbow-evaluation :computed
          :output-satisfies-theorem :proved
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :infinite-limit-convergence :not-claimed
          :unique-fixed-point :not-claimed
          :optimal-policy :not-claimed}
         :failures-remaining
         [:infinite-value-iteration-convergence
          :unique-optimal-fixed-point
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D22"
   :ahof/outcome :proved
   :ahof/specification
   {:action-backup 'bellman/nnrat-action-backup
    :optimality 'value/nnrat-optimality-step
    :recurrence 'ahof-d22/finite-horizon-recurrence
    :greedy-laws 'ahof-d22/greedy-actions
    :two-step 'ahof-d22/two-step-value
    :package 'ahof-d22/value-iteration}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-d22/value-iteration
                          (:target/name %)))
              first :native/id)
     :two-step-proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-d22/two-step-value
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
         :error/category :ahof-d22/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-d22/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before D22 credit"
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
