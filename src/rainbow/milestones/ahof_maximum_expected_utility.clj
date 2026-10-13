(ns rainbow.milestones.ahof-maximum-expected-utility
  "Precommitted leverage evidence for AHoF D17 maximum expected utility."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-decision-guarantee :as audit]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-argmax :as argmax]
            [rainbow.math.logic.maximum-expected-utility :as meu]))

(def precommit-path
  "artifacts/ahof/d17-maximum-expected-utility/precommit.edn")
(def report-path
  "artifacts/ahof/d17-maximum-expected-utility/report.edn")
(def checkpoint-path
  "artifacts/ahof/d17-maximum-expected-utility/checkpoint.edn.gz")
(def default-input-checkpoint-path audit/checkpoint-path)

(def target-support
  {'nat/decide-at-most-true-sound 'nat/decide-at-most-true-sound
   'nnrat/decide-at-most-true-sound 'nnrat/decide-at-most-true-sound
   'decision/nnrat-select-left-bound 'decision/nnrat-select-left-bound
   'list/nnrat-argmax-from-bounds-initial
   'list/nnrat-argmax-from-bounds-initial
   'ahof-d17/probabilities-normalized 'ahof-d17/probabilities-normalized
   'nat/decide-at-most-false-reverse 'nat/decide-at-most-false-reverse
   'nnrat/decide-at-most-false-reverse
   'nnrat/decide-at-most-false-reverse
   'decision/nnrat-select-right-bound 'decision/nnrat-select-right-bound
   'list/nnrat-argmax-from-bounds-member
   'list/nnrat-argmax-from-bounds-member
   'ahof-d17/maximum-expected-utility
   'ahof-d17/maximum-expected-utility
   'decision/finite-nnrat-argmax-is-member
   'decision/finite-nnrat-argmax-is-member
   'decision/finite-nnrat-argmax-dominates
   'decision/finite-nnrat-argmax-dominates})

(def generalized-theorems
  #{'nat/decide-at-most-true-sound
    'nat/decide-at-most-false-reverse
    'nnrat/at-most-rewrite-left
    'nnrat/decide-at-most-true-sound
    'nnrat/decide-at-most-false-reverse
    'decision/nnrat-select-is-left-or-right
    'decision/nnrat-select-left-bound
    'decision/nnrat-select-right-bound
    'list/nnrat-argmax-from-bounds-initial
    'list/nnrat-argmax-from-bounds-member
    'list/nnrat-argmax-from-is-initial-or-member
    'decision/finite-nnrat-argmax-is-member
    'decision/finite-nnrat-argmax-dominates})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "AHoF D17 precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

(defn- timed [operation]
  (let [started (System/nanoTime)
        value (operation)]
    {:value value
     :wall-ms (long (/ (- (System/nanoTime) started) 1000000))}))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- dependency-closure [checked-environment root-id]
  (loop [pending (list root-id) seen #{}]
    (if-let [id (first pending)]
      (if (contains? seen id)
        (recur (rest pending) seen)
        (recur (concat (get-in checked-environment
                               [:rainbow.environment/declarations id
                                :rainbow/dependencies])
                       (rest pending))
               (conj seen id)))
      seen)))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "AHoF D17 input checkpoint rejected" {:prior prior})))
    (let [baseline (:environment prior)
          candidate-timed
          (timed #(-> baseline
                      argmax/extend-environment
                      meu/extend-environment))
          checked-environment (:value candidate-timed)
          definition-ids
          (merge (argmax/definition-ids checked-environment)
                 (meu/definition-ids checked-environment))
          theorem-ids
          (merge (argmax/theorem-ids checked-environment)
                 (meu/theorem-ids checked-environment))
          partitions
          (into {} (map (juxt :target/name :study/partition))
                (:precommit/targets precommit))
          targets
          (mapv
           (fn [[target-name support-name]]
             (let [id (environment/resolve-id checked-environment support-name)]
               {:target/name target-name
                :study/partition (get partitions target-name)
                :native/id id
                :baseline/status
                (if (environment/resolve-id baseline support-name)
                  :proved :missing-representation)
                :candidate/status (if (checked? checked-environment id)
                                    :proved :failed)
                :axioms (kernel/axioms checked-environment id)
                :states-created 0}))
           (sort-by key target-support))
          selected-id (environment/resolve-id checked-environment
                                              'ahof-d17/selected-action)
          renegotiate-id (environment/resolve-id checked-environment
                                                 'ahof-d17/renegotiate)
          evaluation-timed
          (timed
           #(let [selected (kernel/normalize checked-environment
                                             [:const selected-id []]
                                             {:reductions 1000000})
                  renegotiate (kernel/normalize checked-environment
                                                [:const renegotiate-id []]
                                                {:reductions 1000000})]
              {:status (if (and (= :normalized (:status selected))
                                (= (:term selected) (:term renegotiate)))
                         :normalized :failed)
               :selected-action :renegotiate
               :mathematical-theorem
               (get theorem-ids 'ahof-d17/maximum-expected-utility)
               :rainbow-evaluation true
               :clojure-correspondence :not-claimed
               :output-satisfies-theorem
               (get theorem-ids 'ahof-d17/selected-is-renegotiate)}))]
      {:precommit precommit :prior prior :baseline-environment baseline
       :environment checked-environment
       :candidate-build-wall-ms (:wall-ms candidate-timed)
       :evaluation-wall-ms (:wall-ms evaluation-timed)
       :targets targets :definition-ids definition-ids
       :theorem-ids theorem-ids :evaluation (:value evaluation-timed)})))

(defn checkpoint [build]
  (let [value
        (frontier/checkpoint
         {:prior (:prior build) :environment (:environment build)
          :new-mappings [] :evaluations []})
        source-entry
        {:kind :ahof-d17-maximum-expected-utility
         :precommit/id (get-in build [:precommit :precommit/id])
         :proof-values :redacted}
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in [:source :additional-statement-batches]
                       (fnil conj []) source-entry))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn report [build checkpoint-value replay]
  (let [targets (:targets build)
        held-out (filterv #(= :held-out (:study/partition %)) targets)
        transfer (filterv #(= :transfer (:study/partition %)) targets)
        proved? #(= :proved (:candidate/status %))
        generalized-ids (select-keys (:theorem-ids build)
                                     generalized-theorems)
        leverage
        (into
         (sorted-map)
         (map
          (fn [[name id]]
            [name
             {:proof-id id
              :newly-solved-targets
              (->> targets
                   (filter
                    (fn [target]
                      (contains?
                       (dependency-closure (:environment build)
                                           (:native/id target)) id)))
                   (mapv :target/name))}]))
         generalized-ids)
        all-new-ids (concat (vals (:definition-ids build))
                            (vals (:theorem-ids build)))
        passed?
        (and (= :replayed (:status replay))
             (= 12 (count targets))
             (every? proved? targets)
             (every? #(= :missing-representation (:baseline/status %))
                     targets)
             (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (= :normalized (get-in build [:evaluation :status])))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id "D17"
         :algorithm/name "Maximum Expected Utility"
         :source
         {:proof-origin :independent-native-rainbow
          :ahof/source-commit ahof/source-commit
          :mathlib-proof-bodies-used? false
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])
          :precommit/id (get-in build [:precommit :precommit/id])}
         :results
         {:newly-solved-native-results 12
          :newly-solved-exact-or-mappings 1
          :held-out {:before [0 (count held-out)]
                     :after [(count (filter proved? held-out))
                             (count held-out)]}
          :transfer {:after [(count (filter proved? transfer))
                             (count transfer)]}
          :search-states {:median 0 :total 0
                          :interpretation
                          :installed-kernel-checked-certificates}
          :wall-time
          {:rainbow-build-ms (:candidate-build-wall-ms build)
           :rainbow-evaluation-ms (:evaluation-wall-ms build)
           :ai-latency-ms :not-measured-by-offline-runner}
          :lemma-leverage
          {:definition
           :newly-solved-held-out-targets-per-total-introduction-cost
           :held-out-targets-unlocked (count (filter proved? held-out))
           :introduction-cost-ms (:candidate-build-wall-ms build)
           :targets-unlocked-per-generalized-lemma leverage}}
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
         {:mathematical-theorem :proved
          :rainbow-evaluation :computed
          :clojure-correspondence :not-claimed
          :output-satisfies-theorem :proved}
         :not-claimed
         [:production-decision-system :real-valued-probability
          :clojure-program-correspondence :global-argmax-over-infinite-actions]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "D17"
   :ahof/outcome :proved
   :ahof/specification
   {:normalized-probabilities 'ahof-d17/probabilities-normalized
    :finite-expectation-correspondence
    'ahof-d17/expected-utility-is-finite-expectation
    :maximum 'ahof-d17/maximum-expected-utility}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id (get-in packet [:evaluation :mathematical-theorem])}]})

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        checkpoint-value (checkpoint build)
        replay (day54/replay-checkpoint checkpoint-value)
        packet (report build checkpoint-value replay)]
    {:build build :checkpoint checkpoint-value :replay replay :report packet}))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :evidence/id))]
      (if (= expected (:evidence/id value))
        {:status :replayed :evidence/id expected :report value}
        {:status :rejected :error/category :ahof-d17/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :ahof-d17/evidence-read-failed
       :message (.getMessage throwable)})))

(defn- write-edn! [path value]
  (let [file (io/file path)]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

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
          (throw (ex-info "AHoF ledger rejected before D17 credit"
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
