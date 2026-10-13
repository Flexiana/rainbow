(ns rainbow.milestones.ahof-gradient-ascent
  "Content-addressed precommitted evidence for AHoF D49 gradient ascent."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-async-value-iteration :as d23]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gradient-ascent :as specialization]
            [rainbow.algorithms.proofs.gradient-ascent :as iteration]
            [rainbow.algorithms.reference.gradient-ascent :as executable]))

(def precommit-path "artifacts/ahof/d49-gradient-ascent/precommit.edn")
(def report-path "artifacts/ahof/d49-gradient-ascent/report.edn")
(def checkpoint-path "artifacts/ahof/d49-gradient-ascent/checkpoint.edn.gz")
(def default-input-checkpoint-path d23/checkpoint-path)

(def target-support
  (into (sorted-map)
        (map (fn [name] [name name]))
        '[nat/recursor-successor-constant
          nnrat/equivalent-reflexive
          optimization/nnrat-ascent-step
          optimization/nnrat-ascent-iterate
          optimization/nnrat-ascent-step-unfold
          optimization/nnrat-ascent-iterate-successor
          optimization/nnrat-ascent-iterate-zero
          ahof-d49/gradient-ascent-recurrence
          ahof-d49/worked-trajectory
          ahof-d49/gradient-ascent
          optimization/nnrat-ascent-step-transfer]))

;; Worked reference: constant unit gradient, rate 1/2, from the origin.
(def worked-gradient (constantly 1))
(def worked-rate 1/2)
(def worked-initial 0)

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "D49 precommit identity mismatch"
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

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "D49 evaluation expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- equivalent-by-normalization?
  [checked-environment actual expected]
  (let [numerator [:const 'nnrat/numerator []]
        denominator [:const 'nnrat/denominator []]
        multiply [:const 'nat/multiply []]
        left [:app multiply [:app numerator actual] [:app denominator expected]]
        right [:app multiply [:app numerator expected] [:app denominator actual]]
        left-result (kernel/normalize checked-environment
                                      (core checked-environment left)
                                      {:reductions 1000000})
        right-result (kernel/normalize checked-environment
                                       (core checked-environment right)
                                       {:reductions 1000000})]
    (and (= :normalized (:status left-result))
         (= :normalized (:status right-result))
         (= (:term left-result) (:term right-result)))))

(defn- worked-evaluation [checked-environment]
  (let [trajectory [:const 'ahof-d49/trajectory []]
        make (fn [n dp] [:app [:const 'nnrat/make []] n dp])
        dnat (fn [n] (nth (iterate #(vector :app [:const 'data/succ []] %)
                                   [:const 'data/zero []]) n))
        cases [{:step 1 :expected (make (dnat 1) (dnat 1))}
               {:step 2 :expected [:const 'nnrat/one []]}
               {:step 3 :expected (make (dnat 3) (dnat 1))}]
        values
        (mapv
         (fn [{:keys [step expected]}]
           {:step step
            :matches? (equivalent-by-normalization?
                       checked-environment
                       [:app trajectory (dnat step)] expected)})
         cases)
        clojure-trajectory
        (executable/trajectory worked-gradient worked-rate worked-initial 3)]
    {:status (if (and (every? :matches? values)
                      (= [0 1/2 1 3/2] clojure-trajectory))
               :normalized :failed)
     :rainbow {:values values :bounded-steps 3
               :gradient :constant-unit :rate :one-half}
     :clojure-reference
     {:status :computed
      :trajectory clojure-trajectory
      :arithmetic :exact-rational
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "D49 input checkpoint rejected" {:prior prior})))
    (when-not (= (get-in precommit [:precommit/source :input-checkpoint/id])
                 (:checkpoint/id prior))
      (throw (ex-info "D49 input checkpoint identity mismatch"
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
             {:kind :ahof-d49-gradient-ascent
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
             (= 4 (count held-out))
             (= 1 (count transfer))
             (every? proved? targets)
             (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (get-in build [:evaluation :status])))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id "D49"
         :algorithm/name "Gradient Ascent Update"
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
           :shared-prerequisites ['nat/recursor-successor-constant]}}
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
          :bounded-iteration :proved
          :pluggable-gradient :proved
          :ascent-recurrence :proved
          :worked-exact-trajectory :proved
          :rainbow-evaluation :computed
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :convergence-to-optimum :not-claimed
          :step-size-schedule :not-claimed
          :signed-gradient :not-claimed}
         :failures-remaining
         [:convergence-to-optimum
          :adaptive-step-size-schedules
          :signed-gradient-domain
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D49"
   :ahof/outcome :proved
   :ahof/specification
   {:ascent-step 'optimization/nnrat-ascent-step
    :ascent-iterate 'optimization/nnrat-ascent-iterate
    :successor 'optimization/nnrat-ascent-iterate-successor
    :recurrence 'ahof-d49/gradient-ascent-recurrence
    :trajectory 'ahof-d49/worked-trajectory
    :package 'ahof-d49/gradient-ascent}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-d49/gradient-ascent (:target/name %)))
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
        {:status :rejected :error/category :ahof-d49/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-d49/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before D49 credit"
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
