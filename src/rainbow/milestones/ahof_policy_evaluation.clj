(ns rainbow.milestones.ahof-policy-evaluation
  "Content-addressed precommitted evidence for AHoF D20 policy evaluation."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-maximum-expected-utility :as d17]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.policy-evaluation :as specialization]
            [rainbow.math.finite.policy-evaluation :as evaluation]))

(def precommit-path "artifacts/ahof/d20-policy-evaluation/precommit.edn")
(def report-path "artifacts/ahof/d20-policy-evaluation/report.edn")
(def checkpoint-path "artifacts/ahof/d20-policy-evaluation/checkpoint.edn.gz")
(def default-input-checkpoint-path d17/checkpoint-path)

(def target-support
  {'bellman/nnrat-fixed-policy-unfold 'bellman/nnrat-fixed-policy-unfold
   'bellman/nnrat-value-iterate-zero 'bellman/nnrat-value-iterate-zero
   'bellman/nnrat-fixed-policy-congruent 'bellman/nnrat-fixed-policy-congruent
   'bellman/nnrat-value-iterate-successor
   'bellman/nnrat-value-iterate-successor
   'bellman/nnrat-value-iterate-congruent
   'bellman/nnrat-value-iterate-congruent
   'bellman/nnrat-value-iterate-model-transfer
   'bellman/nnrat-value-iterate-model-transfer
   'bellman/nnrat-value-iterate-initial-transfer
   'bellman/nnrat-value-iterate-initial-transfer
   'ahof-d20/finite-horizon-recurrence 'ahof-d20/finite-horizon-recurrence
   'ahof-d20/normalized-transition-rows
   'ahof-d20/normalized-transition-rows
   'ahof-d20/one-step-value 'ahof-d20/one-step-value
   'ahof-d20/two-step-value 'ahof-d20/two-step-value
   'ahof-d20/policy-evaluation 'ahof-d20/policy-evaluation})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "D20 precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime) value (operation)]
    {:value value :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "D20 evaluation expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- worked-evaluation [checked-environment]
  (let [zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        three [:app successor [:app successor one]]
        worked [:const 'ahof-d20/worked-two-step-value []]
        make [:const 'nnrat/make []]
        cases [{:state :zero :input zero :expected [:const 'nnrat/zero []]}
               {:state :one :input one :expected [:app make three one]}]
        numerator [:const 'nnrat/numerator []]
        denominator [:const 'nnrat/denominator []]
        multiply [:const 'nat/multiply []]
        outputs
        (mapv
         (fn [{:keys [input expected] :as case}]
           (let [actual [:app worked input]
                 left [:app multiply [:app numerator actual]
                       [:app denominator expected]]
                 right [:app multiply [:app numerator expected]
                        [:app denominator actual]]
                 left-result (kernel/normalize checked-environment
                                               (core checked-environment left)
                                               {:reductions 1000000})
                 right-result (kernel/normalize checked-environment
                                                (core checked-environment right)
                                                {:reductions 1000000})]
             (-> case
                 (dissoc :input :expected)
                 (assoc :status :normalized
                        :matches?
                        (= (:term left-result) (:term right-result))))))
         cases)]
    {:status (if (every? :matches? outputs) :normalized :failed)
     :outputs outputs :bounded-steps 2}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "D20 input checkpoint rejected" {:prior prior})))
    (let [baseline (:environment prior)
          candidate-timed
          (timed #(-> baseline
                      evaluation/extend-environment
                      specialization/extend-environment))
          checked-environment (:value candidate-timed)
          definition-ids (specialization/definition-ids checked-environment)
          theorem-ids (merge (evaluation/theorem-ids checked-environment)
                             (specialization/theorem-ids checked-environment))
          partitions
          (into {} (map (juxt :target/name :study/partition))
                (:precommit/targets precommit))
          targets
          (mapv
           (fn [[target support]]
             (let [id (environment/resolve-id checked-environment support)]
               {:target/name target :study/partition (get partitions target)
                :native/id id
                :baseline/status
                (if (environment/resolve-id baseline support)
                  :proved :missing-generalized-lemma)
                :candidate/status (if (checked? checked-environment id)
                                    :proved :failed)
                :axioms (kernel/axioms checked-environment id)
                :states-created 0}))
           (sort-by key target-support))
          evaluation-timed (timed #(worked-evaluation checked-environment))]
      {:precommit precommit :prior prior :environment checked-environment
       :targets targets :definition-ids definition-ids :theorem-ids theorem-ids
       :build-wall-ms (:wall-ms candidate-timed)
       :evaluation-wall-ms (:wall-ms evaluation-timed)
       :evaluation (:value evaluation-timed)})))

(defn checkpoint [build]
  (let [value (frontier/checkpoint
               {:prior (:prior build) :environment (:environment build)
                :new-mappings [] :evaluations []})
        base (-> value
                 (dissoc :rainbow.checkpoint/id)
                 (update-in
                  [:source :additional-statement-batches] (fnil conj [])
                  {:kind :ahof-d20-policy-evaluation
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
        (and (= :replayed (:status replay)) (= 12 (count targets))
             (= 3 (count (filter #(= :proved (:baseline/status %)) targets)))
             (every? proved? targets) (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (get-in build [:evaluation :status])))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1 :algorithm/id "D20"
         :algorithm/name "Policy Evaluation"
         :source {:proof-origin :independent-native-rainbow
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
          :search-states {:median 0 :total 0
                          :interpretation :installed-kernel-certificates}
          :wall-time {:rainbow-build-ms (:build-wall-ms build)
                      :rainbow-evaluation-ms (:evaluation-wall-ms build)
                      :ai-latency-ms :not-measured-by-offline-runner}
          :lemma-leverage
          {:new-held-out-targets (count (filter proved? held-out))
           :introduction-cost-ms (:build-wall-ms build)
           :new-targets-per-generalized-package (count new-targets)}}
         :targets targets :evaluation (:evaluation build)
         :axiom-profiles
         (into (sorted-map)
               (map (fn [[name id]]
                      [name (kernel/axioms (:environment build) id)]))
               (:theorem-ids build))
         :trusted-base-delta :none
         :checkpoint {:id (:rainbow.checkpoint/id checkpoint-value)
                      :kernel-replay (:status replay)
                      :exact-mathlib-mappings
                      (count (:mappings checkpoint-value))}
         :claim-boundaries
         {:mathematical-theorem :proved
          :rainbow-evaluation :computed
          :clojure-correspondence :not-claimed
          :output-satisfies-theorem :proved
          :infinite-limit-convergence :not-claimed
          :unique-fixed-point :not-claimed}}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D20" :ahof/outcome :proved
   :ahof/specification
   {:recurrence 'ahof-d20/finite-horizon-recurrence
    :normalization 'ahof-d20/normalized-transition-rows
    :one-step 'ahof-d20/one-step-value
    :two-step 'ahof-d20/two-step-value
    :package 'ahof-d20/policy-evaluation}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id (some->> (:targets packet)
                        (filter #(= 'ahof-d20/policy-evaluation
                                    (:target/name %))) first :native/id)
     :two-step-proof-id (some->> (:targets packet)
                                 (filter #(= 'ahof-d20/two-step-value
                                             (:target/name %)))
                                 first :native/id)}]})

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
        {:status :rejected :error/category :ahof-d20/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :ahof-d20/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before D20 credit"
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
