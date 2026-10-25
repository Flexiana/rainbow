(ns rainbow.milestones.ahof-pattern-search
  "Content-addressed precommitted evidence for AHoF O35 generalized pattern search."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-trust-region :as o16]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.pattern-search :as specialization]
            [rainbow.algorithms.proofs.pattern-search :as iteration]
            [rainbow.algorithms.reference.pattern-search :as executable]))

(def precommit-path "artifacts/ahof/o35-pattern-search/precommit.edn")
(def report-path "artifacts/ahof/o35-pattern-search/report.edn")
(def checkpoint-path "artifacts/ahof/o35-pattern-search/checkpoint.edn.gz")
(def default-input-checkpoint-path o16/checkpoint-path)

(def target-support
  (into (sorted-map)
        (map (fn [name] [name name]))
        '[audit/decide-nnrat-at-most
          logic/if-data
          search/poll-better
          search/poll-improves
          search/pattern-move
          search/poll-better-unfold
          search/pattern-move-unfold
          ahof-o35/poll-picks-backward
          ahof-o35/move-accepts-best
          ahof-o35/pattern-search
          search/poll-improves-unfold]))

;; Worked pattern search: minimize x^2 from x=2, step 1, polling 3 and 1.
(def worked-objective (fn [x] (* x x)))
(def worked-current 2)
(def worked-forward 3)
(def worked-backward 1)

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "O35 precommit identity mismatch"
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
  (let [polled (executable/poll-better (worked-objective worked-forward)
                                       (worked-objective worked-backward)
                                       worked-forward worked-backward)
        moved (executable/step worked-objective worked-current worked-forward
                               worked-backward)]
    {:status (if (and (= 1 polled) (= 1 moved)) :normalized :failed)
     :rainbow {:polled-best :backward-one :moved-to :backward-one}
     :clojure-reference
     {:status :computed
      :forward-objective (worked-objective worked-forward)
      :backward-objective (worked-objective worked-backward)
      :current-objective (worked-objective worked-current)
      :polled-best polled
      :moved-to moved
      :derivative-free true
      :arithmetic :exact-rational
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "O35 input checkpoint rejected" {:prior prior})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "O35 input checkpoint identity mismatch"
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
             {:kind :ahof-o35-pattern-search
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
         :algorithm/id "O35"
         :algorithm/name "Generalized Pattern Search"
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
           :shared-prerequisites ['search/poll-better 'search/pattern-move]}}
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
          :derivative-free-poll :proved
          :argmin-selection :proved
          :improvement-accept :proved
          :rainbow-evaluation :computed
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :arbitrary-pattern :not-claimed
          :mesh-refinement :not-claimed
          :convergence :not-claimed}
         :failures-remaining
         [:arbitrary-pattern-of-directions
          :mesh-refinement-schedule
          :convergence-theorem
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "O35"
   :ahof/outcome :proved
   :ahof/specification
   {:poll 'search/poll-better
    :improves 'search/poll-improves
    :move 'search/pattern-move
    :worked-poll 'ahof-o35/poll-picks-backward
    :package 'ahof-o35/pattern-search}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-o35/pattern-search (:target/name %)))
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
        {:status :rejected :error/category :ahof-o35/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-o35/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before O35 credit"
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
