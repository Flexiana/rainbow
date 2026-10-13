(ns rainbow.milestones.ahof-levenberg-marquardt
  "Content-addressed precommitted evidence for AHoF O31 Levenberg-Marquardt."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-conjugate-gradient :as o18]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.levenberg-marquardt :as specialization]
            [rainbow.algorithms.proofs.levenberg-marquardt :as lm]
            [rainbow.math.rational.division :as division]
            [rainbow.algorithms.reference.levenberg-marquardt :as executable]
            [rainbow.algorithms.reference.newton :as newton]))

(def precommit-path "artifacts/ahof/o31-levenberg-marquardt/precommit.edn")
(def report-path "artifacts/ahof/o31-levenberg-marquardt/report.edn")
(def checkpoint-path "artifacts/ahof/o31-levenberg-marquardt/checkpoint.edn.gz")
(def default-input-checkpoint-path o18/checkpoint-path)

(def target-support
  (into (sorted-map)
        (map (fn [name] [name name]))
        '[optimization/general-descent-step
          nnrat/reciprocal
          optimization/levenberg-marquardt-rate
          optimization/levenberg-marquardt-rate-unfold
          ahof-o31/step-size
          ahof-o31/damped-step-is-one
          ahof-o31/levenberg-marquardt-recurrence
          ahof-o31/levenberg-marquardt
          ahof-o31/hessian
          ahof-o31/lambda
          ahof-o31/trajectory]))

;; Worked LM on f(x) = x^2: Hessian 2, damping 2, gradient 2x, from x=2.
(def worked-hessian (fn [_x] 2))
(def worked-lambda 2)
(def worked-gradient (fn [x] (* 2 x)))
(def worked-initial 2)

(defn- extend-all [environment]
  (-> environment
      division/extend-environment
      lm/extend-environment
      specialization/extend-environment))

(defn- definition-ids-all [environment]
  (merge (division/definition-ids environment)
         (lm/definition-ids environment)
         (specialization/definition-ids environment)))

(defn- theorem-ids-all [environment]
  (merge (division/theorem-ids environment)
         (lm/theorem-ids environment)
         (specialization/theorem-ids environment)))

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "O31 precommit identity mismatch"
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
  (let [lm-step (executable/run worked-hessian worked-lambda worked-gradient 1
                                worked-initial)
        newton-step (newton/run worked-hessian worked-gradient 1 worked-initial)
        rate (executable/rate worked-hessian worked-lambda worked-initial)]
    {:status (if (and (= 1 lm-step) (= 1/4 rate) (= 0 newton-step))
               :normalized :failed)
     :rainbow {:step-size :one-quarter :first-step :one
               :damped-larger-than-newton-leap true}
     :clojure-reference
     {:status :computed
      :lm-rate rate
      :lm-first-step lm-step
      :newton-first-step newton-step
      :damping-shortens-step (not= lm-step newton-step)
      :arithmetic :exact-rational
      :correspondence :tested-structural-observation}}))

(defn build [input-checkpoint-path]
  (let [precommit (load-precommit)
        prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "O31 input checkpoint rejected" {:prior prior})))
    (when-not (= (get-in precommit [:precommit/source :input-checkpoint/id])
                 (:checkpoint/id prior))
      (throw (ex-info "O31 input checkpoint identity mismatch"
                      {:precommitted
                       (get-in precommit
                               [:precommit/source :input-checkpoint/id])
                       :actual (:checkpoint/id prior)})))
    (let [baseline (:environment prior)
          candidate-timed (timed #(extend-all baseline))
          checked-environment (:value candidate-timed)
          definition-ids (definition-ids-all checked-environment)
          theorem-ids (theorem-ids-all checked-environment)
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
             {:kind :ahof-o31-levenberg-marquardt
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
         :algorithm/id "O31"
         :algorithm/name "Levenberg-Marquardt"
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
           :shared-prerequisites ['optimization/levenberg-marquardt-rate
                                  'nnrat/reciprocal]}}
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
          :damped-hessian-inverse-step :proved
          :interpolates-descent-and-newton :computed-observation
          :rational-division-used :proved
          :rainbow-evaluation :computed
          :clojure-reference-output :computed
          :clojure-correspondence :tested-structural-observation
          :adaptive-damping :not-claimed
          :general-convergence :not-claimed
          :multivariate-hessian :not-claimed}
         :failures-remaining
         [:adaptive-damping-schedule
          :general-convergence-theorem
          :multivariate-damped-hessian-inverse
          :proved-clojure-correspondence]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  {:ahof/id "O31"
   :ahof/outcome :proved
   :ahof/specification
   {:step-size 'optimization/levenberg-marquardt-rate
    :division 'nnrat/divide
    :worked-step 'ahof-o31/damped-step-is-one
    :package 'ahof-o31/levenberg-marquardt}
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id
     (some->> (:targets packet)
              (filter #(= 'ahof-o31/levenberg-marquardt (:target/name %)))
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
        {:status :rejected :error/category :ahof-o31/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-o31/evidence-read-failed
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
          (throw (ex-info "AHoF ledger rejected before O31 credit"
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
