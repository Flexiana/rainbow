(ns rainbow.history.held-out-retrieval
  "Measured held-out theorem retrieval and kernel-checked reuse."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(def training-budget {:states 2000 :depth 32 :wall-ms 10000})
(def evaluation-budget {:states 3 :depth 32 :wall-ms 10000})
(def report-path "artifacts/day20/report.edn")

(def held-out-targets
  (mapv (fn [{:keys [name type]}]
          {:name (symbol "held-out-reuse" (clojure.core/name name))
           ;; The additional, unused proposition makes each evaluation statement
           ;; distinct from its indexed training theorem.
           :type [:pi [:sort [:zero]] type :explicit]})
        (take 10 first-tactic-program/development-targets)))

(def retrieval-policy
  {:allowed-axioms #{}
   :allowed-sources #{:native}
   :denied-dependencies #{}
   :required-concepts #{:shape/pi}})

(defn train []
  (first-tactic-program/run-targets (direct-term-corpus/build-environment)
                    first-tactic-program/development-targets
                    training-budget))

(defn- prove-held-out [checked-environment index target reuse?]
  (let [started (proof/start checked-environment (:type target))]
    (assoc (search/prove (:state started)
                         (cond-> evaluation-budget
                           reuse? (assoc :reuse-index index
                                         :reuse-policy retrieval-policy)))
           :evaluation/budget evaluation-budget
           :job/id (:name target)
           :target target)))

(defn- run-evaluation [checked-environment index reuse?]
  (mapv #(prove-held-out checked-environment index % reuse?) held-out-targets))

(defn- successful-reuse-ids [results]
  (mapv #(get-in % [:strategy :declaration/id])
        (filter #(and (= :success (:result %))
                      (= :reuse (get-in % [:strategy :tactic])))
                (mapcat :attempts results))))

(defn- register-results [checked-environment results]
  (reduce (fn [{:keys [environment declarations] :as state} result]
            (let [proof-term (get-in result [:proof :proof/term])
                  proof-type (get-in result [:proof :proof/type])
                  registration
                  (kernel/add-declaration
                   environment
                   {:rainbow/kind :theorem
                    :rainbow/aliases #{(:job/id result)}
                    :rainbow/universes []
                    :rainbow/type proof-type
                    :rainbow/value proof-term
                    :rainbow/transparency :opaque
                    :rainbow/dependencies (into (term/constants proof-type)
                                                (term/constants proof-term))
                    :rainbow/provenance {:origin :native
                                         :producer :measured-theorem-reuse}
                    :rainbow/schema-version 1})]
              (if (= :accepted (:status registration))
                {:status :accepted
                 :environment (:environment registration)
                 :declarations (conj declarations (:declaration registration))}
                (reduced (assoc state :status :rejected :cause registration)))))
          {:status :accepted :environment checked-environment :declarations []}
          results))

(defn experiment []
  (let [training (train)
        checked-environment (:environment training)
        training-ids (mapv #(get-in % [:declaration :rainbow/id])
                           (:results training))
        index (reuse/build-index checked-environment {:include-ids training-ids})
        baseline (run-evaluation checked-environment index false)
        with-reuse (run-evaluation checked-environment index true)
        reuse-ids (successful-reuse-ids with-reuse)
        uses (frequencies reuse-ids)
        zero-use-ids (into #{} (remove #(pos? (get uses % 0))) training-ids)
        lifecycle (into {}
                        (map (fn [id]
                               [id {:status :quarantined
                                    :reason :evaluation/zero-held-out-use}]))
                        zero-use-ids)
        evidence (into {}
                       (map (fn [id]
                              [id {:successful-uses (get uses id 0)
                                   :failed-uses 0}]))
                       training-ids)
        evaluated-index (reuse/build-index checked-environment
                                           {:include-ids training-ids
                                            :lifecycle lifecycle
                                            :evidence evidence})
        quarantined-id (first (sort zero-use-ids))
        quarantined-declaration (environment/declaration checked-environment
                                                         quarantined-id)
        quarantine-query (reuse/query evaluated-index checked-environment
                                      (:rainbow/type quarantined-declaration)
                                      retrieval-policy)
        registrations (register-results checked-environment with-reuse)]
    {:training training
     :training-ids training-ids
     :index index
     :baseline baseline
     :with-reuse with-reuse
     :reuse-ids reuse-ids
     :uses uses
     :zero-use-ids zero-use-ids
     :evaluated-index evaluated-index
     :quarantine-query quarantine-query
     :registrations registrations}))

(defn- result-summary [results]
  {:goals (count results)
   :proved (count (filter #(= :proved (:status %)) results))
   :blocked (count (filter #(= :blocked (:status %)) results))
   :states-created (reduce + (map #(get-in % [:telemetry :states-created] 0)
                                   results))
   :kernel-checks (reduce + (map #(get-in % [:telemetry :kernel-checks] 0)
                                 results))
   :reuse-lookups (reduce + (map #(get-in % [:telemetry :reuse-lookups] 0)
                                 results))
   :reuse-attempts (reduce + (map #(get-in % [:telemetry :reuse-attempts] 0)
                                  results))
   :reuse-successes (reduce + (map #(get-in % [:telemetry :reuse-successes] 0)
                                   results))})

(defn report []
  (let [{:keys [training training-ids index baseline with-reuse reuse-ids
                zero-use-ids evaluated-index quarantine-query registrations]}
        (experiment)
        baseline-summary (result-summary baseline)
        reuse-summary (result-summary with-reuse)
        registered (:declarations registrations)
        kernel-rechecked (count (filter #(= :checked (get-in % [:kernel :status]))
                                        with-reuse))
        axiom-free (count (filter #(empty? (:rainbow/axioms %)) registered))
        ordinary-const-reuses
        (count (filter #(and (= :reuse (get-in % [:strategy :tactic]))
                             (= :const (first (get-in % [:strategy :term]))))
                       (mapcat :attempts with-reuse)))
        passed? (and (= :passed (:status training))
                     (= 12 (count training-ids))
                     (= 0 (:proved baseline-summary))
                     (= 10 (:proved reuse-summary))
                     (= 10 kernel-rechecked axiom-free ordinary-const-reuses)
                     (= :accepted (:status registrations))
                     (= 10 (count (distinct reuse-ids)))
                     (= 2 (count zero-use-ids))
                     (empty? (:candidates quarantine-query)))
        base
        {:status (if passed? :passed :failed)
         :benchmark {:split {:training-theorems 12 :held-out-goals 10}
                     :same-goals true
                     :same-seed :deterministic-breadth-first
                     :same-budget evaluation-budget
                     :baseline baseline-summary
                     :reuse reuse-summary
                     :solve-rate-delta (- (:proved reuse-summary)
                                          (:proved baseline-summary))}
         :retrieval {:index/id (:reuse/id index)
                     :environment/id (:reuse/environment-id index)
                     :method :exact-normalized-type
                     :policy retrieval-policy
                     :ranking-components
                     [:exact-normalized-type :concept-overlap :dependency-overlap
                      :successful-uses :failed-uses]
                     :ordinary-const-proof-terms ordinary-const-reuses
                     :kernel-rechecked kernel-rechecked
                     :axiom-free-registrations axiom-free}
         :lifecycle {:evaluated-index/id (:reuse/id evaluated-index)
                     :active (- (count training-ids) (count zero-use-ids))
                     :quarantined (count zero-use-ids)
                     :reason :evaluation/zero-held-out-use
                     :quarantined-query-results (count (:candidates quarantine-query))}
         :proof-capacity {:distinct-held-out-theorems-added (count registered)
                          :training-theorems-reused (count (distinct reuse-ids))}
         :claim-boundaries
         {:supported :monomorphic-exact-normalized-subgoal
          :universe-polymorphic-retrieval :explicitly-quarantined
          :approximate-or-learned-retrieval :not-implemented
          :trusted-base-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :reuse/report-id-mismatch
         :expected expected :actual (:report/id value)}))
    (catch Throwable throwable
      {:status :rejected :error/category :reuse/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report)))
    "replay" (let [result (load-report (or path report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
