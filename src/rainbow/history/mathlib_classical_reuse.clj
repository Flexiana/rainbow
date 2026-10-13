(ns rainbow.history.mathlib-classical-reuse
  "Axiom-relative classical proof reuse over the current Mathlib residual set."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-binder-aware-reuse :as mathlib-binder-aware-reuse]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.classical :as classical]
            [rainbow.math.profile :as profile]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day40/report.edn")
(def default-catalog-path mathlib-binder-aware-reuse/default-catalog-path)
(def default-statement-path mathlib-binder-aware-reuse/default-statement-path)
(def requested-foreign-names mathlib-binder-aware-reuse/requested-foreign-names)
(def constant-aliases mathlib-binder-aware-reuse/constant-aliases)
(def evaluation-budget {:states 4 :depth 4 :wall-ms 1000})

(defn- nativeized-residuals [checked-environment statements proved-names]
  (vec
   (keep
    (fn [statement]
      (let [result
            (mathlib-native/nativeize-statement-type
             checked-environment statement {:constant-aliases constant-aliases})]
        (when (and (= :nativeized (:status result))
                   (not (contains? proved-names (:foreign/name result))))
          result)))
    statements)))

(defn- prove-match [checked-environment index reuse-policy target]
  (let [query (reuse/query index checked-environment (:type target) reuse-policy)]
    (when (pos? (:returned query))
      (when-not (= 1 (:returned query))
        (throw (ex-info "Day 40 target had ambiguous exact reuse"
                        {:target (:foreign/name target) :query query})))
      (let [result
            (search/prove
             (:state (proof/start checked-environment (:type target)
                                  {:universes (:universes target)}))
             (assoc evaluation-budget
                    :reuse-index index :reuse-policy reuse-policy))
            candidate (first (:candidates query))
            declaration
            (environment/declaration checked-environment
                                     (:reuse/declaration-id candidate))]
        (when-not (and (= :proved (:status result))
                       (= :checked (get-in result [:kernel :status]))
                       (= 1 (get-in result [:telemetry :reuse-successes])))
          (throw (ex-info "Day 40 exact reuse failed kernel gate"
                          {:target (:foreign/name target) :result result})))
        {:target target :query query :proof result
         :declaration declaration}))))

(defn build [statement-path]
  (let [prior (mathlib-binder-aware-reuse/build)
        base-environment (:environment prior)
        activation (profile/activate base-environment :classical)
        extension (classical/extend-activation activation)
        checked-environment (:environment extension)
        reuse-policy {:allowed-axioms (:logical/axiom-ids activation)}
        index (reuse/build-index checked-environment)
        statements (:statements
                    (mathlib/load-statement-batch statement-path
                                                  requested-foreign-names))
        prior-proved-names (set (map :foreign/name
                                     (mathlib-binder-aware-reuse/all-mappings prior)))
        residuals (nativeized-residuals checked-environment statements
                                        prior-proved-names)
        results (vec (keep #(prove-match checked-environment index reuse-policy %)
                           residuals))]
    {:environment checked-environment
     :prior prior
     :activation activation
     :classical-extension extension
     :reuse-index index
     :reuse-policy reuse-policy
     :residuals residuals
     :results results}))

(defn result-mappings [{:keys [results]}]
  (mapv (fn [{:keys [target declaration]}]
          {:foreign/name (:foreign/name target)
           :native/id (:rainbow/id declaration)})
        results))

(defn all-mappings [{:keys [prior] :as built}]
  (vec (concat (mathlib-binder-aware-reuse/all-mappings prior) (result-mappings built))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        {:keys [environment activation residuals results] :as built}
        (build statement-path)
        mappings (result-mappings built)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-ids (set (map :native/id mappings))
        excluded-middle-id (first (:logical/axiom-ids activation))
        axiom-closures
        (into (sorted-map)
              (map (fn [id] [id (kernel/axioms environment id)]))
              native-ids)
        groups
        (->> mappings
             (group-by :native/id)
             (map (fn [[native-id values]]
                    {:native/id native-id
                     :foreign/names (vec (sort (map :foreign/name values)))}))
             (sort-by :native/id)
             vec)
        new-names (set (map :foreign/name mappings))
        expected-names
        #{"em'" "by_contra" "peirce" "of_not_not" "by_contradiction"
          "Classical.by_cases" "by_cases" "Classical.by_contradiction"}
        remaining (set/difference (set (map :foreign/name residuals)) new-names)
        passed?
        (and (= :verified (:status batch))
             (= 79 (count residuals))
             (= expected-names new-names)
             (= 8 (count results) (count mappings))
             (= 4 (count native-ids) (count groups))
             (= 71 (count remaining))
             (= 89 (:proved summary))
             (= mathlib/pinned-distinct-theorem-count (:theorems summary))
             (every? #(= #{excluded-middle-id} %) (vals axiom-closures))
             (every? #(= :checked (get-in % [:proof :kernel :status])) results)
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit
                  :statement-batch/id (:batch/id batch)
                  :catalog/id (:catalog/id batch)
                  :proof-values :redacted}
         :experiment
         {:residual-targets 79
          :exact-policy-matches 8
          :remaining-targets 71
          :budget evaluation-budget
          :all-kernel-checked? true
          :lean-proofs-visible-to-rainbow? false}
         :proofs
         {:foreign-declarations 8
          :distinct-native-proof-objects 4
          :axiom-free-new-proofs 0
          :classical-relative-new-proofs 4
          :mappings mappings
          :coincident-groups groups
          :axiom-closures axiom-closures
          :logical/profile :classical
          :logical/principles #{:classical}}
         :coverage
         {:exact-statement-mappings (:proved summary)
          :axiom-free 81
          :classical-relative-new 8
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings-id (canonical/content-id all-mappings)}
         :claim-boundaries
         {:excluded-middle/id excluded-middle-id
          :direct-axiom-as-proof-count 0
          :trusted-kernel-change :none}}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :day40/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :day40/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command second-path]]
  (try
    (if (= "replay" command)
      (let [result (load-report (or second-path report-path))]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [value (report (or command default-catalog-path)
                          (or second-path default-statement-path))]
        (println (pr-str value))
        (when-not (= :passed (:status value)) (System/exit 1))))
    (finally (shutdown-agents))))
