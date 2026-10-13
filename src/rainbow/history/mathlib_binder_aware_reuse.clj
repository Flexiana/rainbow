(ns rainbow.history.mathlib-binder-aware-reuse
  "Binder-aware native abstraction reuse over a proof-redacted Mathlib target."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.accounting :as accounting]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-equality-transport :as mathlib-equality-transport]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.reuse :as reuse]
            [rainbow.search :as search]))

(def report-path "artifacts/day37/report.edn")
(def default-catalog-path mathlib-equality-transport/default-catalog-path)
(def default-statement-path mathlib-equality-transport/default-statement-path)
(def requested-foreign-names mathlib-equality-transport/requested-foreign-names)
(def constant-aliases mathlib-equality-transport/constant-aliases)

(def promoted-statement
  {:rainbow.catalog/kind :statement
   :foreign/name "Iff.iff"
   :foreign/module "Mathlib.Logic.Basic"
   :foreign/universes []
   :foreign/type-fingerprint "lean-hash64:1388192255"
   :foreign/type
   [:pi [:sort [:zero]]
    [:pi [:sort [:zero]]
     [:pi [:sort [:zero]]
      [:pi [:sort [:zero]]
       [:pi
        [:app [:app [:const "Iff" []] [:bound 3]] [:bound 2]]
        [:pi
         [:app [:app [:const "Iff" []] [:bound 2]] [:bound 1]]
         [:app
          [:app [:const "Iff" []]
           [:app [:app [:const "Iff" []] [:bound 5]] [:bound 3]]]
          [:app [:app [:const "Iff" []] [:bound 4]] [:bound 2]]]
         :explicit]
        :explicit]
       :implicit]
      :implicit]
     :implicit]
    :implicit]
   :foreign/value :redacted
   :foreign/location nil})

(def evaluation-budget {:states 4 :depth 4 :wall-ms 1000})

(defn- nativeize! [checked-environment statement]
  (let [result
        (mathlib-native/nativeize-statement-type
         checked-environment statement {:constant-aliases constant-aliases})]
    (when-not (= :nativeized (:status result))
      (throw (ex-info "Day 37 statement did not nativeize"
                      {:statement (:foreign/name statement) :result result})))
    result))

(defn build []
  (let [prior (mathlib-equality-transport/build)
        checked-environment (:environment prior)
        nativeized (nativeize! checked-environment promoted-statement)
        index (reuse/build-index checked-environment)
        start #(proof/start checked-environment (:type nativeized)
                            {:universes (:universes nativeized)})
        baseline (search/prove (:state (start)) evaluation-budget)
        with-reuse (search/prove (:state (start))
                                 (assoc evaluation-budget :reuse-index index))
        query (reuse/query index checked-environment (:type nativeized))
        candidate (first (:candidates query))
        declaration-id (:reuse/declaration-id candidate)
        declaration (environment/declaration checked-environment declaration-id)]
    (when-not (and (= :blocked (:status baseline))
                   (= :proved (:status with-reuse))
                   (= :checked (get-in with-reuse [:kernel :status]))
                   (= 1 (:returned query))
                   (= 'proposition/equivalence-congruence
                      (first (:rainbow/aliases declaration))))
      (throw (ex-info "Day 37 held-out reuse gate failed"
                      {:baseline baseline :with-reuse with-reuse
                       :query query :declaration declaration})))
    {:environment checked-environment
     :prior prior
     :reuse-index index
     :result {:statement promoted-statement
              :nativeized nativeized
              :baseline baseline
              :proof with-reuse
              :query query
              :declaration declaration}}))

(defn result-mappings [{:keys [result]}]
  [{:foreign/name (get-in result [:statement :foreign/name])
    :native/id (get-in result [:declaration :rainbow/id])}])

(defn all-mappings [{:keys [prior] :as built}]
  (vec (concat (mathlib-equality-transport/all-mappings prior) (result-mappings built))))

(defn- residual-reuse-evaluation [checked-environment index statements
                                  prior-proved-names]
  (let [nativeized
        (keep (fn [statement]
                (let [result
                      (mathlib-native/nativeize-statement-type
                       checked-environment statement
                       {:constant-aliases constant-aliases})]
                  (when (= :nativeized (:status result)) result)))
              statements)
        residual (remove #(contains? prior-proved-names (:foreign/name %))
                         nativeized)
        queries (mapv (fn [target]
                        {:foreign/name (:foreign/name target)
                         :query (reuse/query index checked-environment
                                             (:type target))})
                      residual)
        matched (filterv #(pos? (get-in % [:query :returned])) queries)]
    {:targets (count residual)
     :universe-free (count (filter #(empty? (:universes %)) residual))
     :universe-polymorphic (count (remove #(empty? (:universes %)) residual))
     :exact-matches (count matched)
     :matched-names (mapv :foreign/name matched)}))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        statements-by-name (into {} (map (juxt :foreign/name identity)
                                         (:statements batch)))
        {:keys [environment prior reuse-index result] :as built} (build)
        prior-mappings (mathlib-equality-transport/all-mappings prior)
        prior-proved-names (set (map :foreign/name prior-mappings))
        residual-evaluation
        (residual-reuse-evaluation environment reuse-index (:statements batch)
                                   prior-proved-names)
        mappings (result-mappings built)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-id (get-in result [:declaration :rainbow/id])
        axioms (kernel/axioms environment native-id)
        search-deferred
        (set/difference
         (set (keep (fn [statement]
                      (let [nativeized
                            (mathlib-native/nativeize-statement-type
                             environment statement
                             {:constant-aliases constant-aliases})]
                        (when (= :nativeized (:status nativeized))
                          (:foreign/name statement))))
                    (:statements batch)))
         proved-names)
        passed?
        (and (= :verified (:status batch))
             (= promoted-statement (get statements-by-name "Iff.iff"))
             (= {:targets 80 :universe-free 59 :universe-polymorphic 21
                 :exact-matches 1 :matched-names ["Iff.iff"]}
                residual-evaluation)
             (= :blocked (get-in result [:baseline :status]))
             (= :proved (get-in result [:proof :status]))
             (= :checked (get-in result [:proof :kernel :status]))
             (= 1 (get-in result [:proof :telemetry :reuse-successes]))
             (= 1 (count mappings)) (= 81 (:proved summary))
             (= mathlib/pinned-distinct-theorem-count (:theorems summary))
             (= 79 (count search-deferred))
             (empty? axioms)
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit
                  :module "Mathlib.Logic.Basic"}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested 128
          :proof-values :redacted}
         :experiment
         {:development-source :cluster-derived-native-abstraction
          :held-out-target "Iff.iff"
          :same-budget evaluation-budget
          :before {:status (get-in result [:baseline :status])
                   :states-created
                   (get-in result [:baseline :telemetry :states-created])
                   :reuse-enabled? false}
          :after {:status (get-in result [:proof :status])
                  :states-created
                  (get-in result [:proof :telemetry :states-created])
                  :reuse-enabled? true
                  :reuse-successes
                  (get-in result [:proof :telemetry :reuse-successes])
                  :kernel-status (get-in result [:proof :kernel :status])}}
         :retrieval
         {:index/id (:reuse/id reuse-index)
          :index-entries (count (:reuse/entries reuse-index))
          :active-entries
          (count (filter #(= :active (get-in % [:reuse/lifecycle :status]))
                         (:reuse/entries reuse-index)))
          :residual-evaluation residual-evaluation
          :matched-native/id native-id
          :matched-native/alias 'proposition/equivalence-congruence
          :matched-type-key (get-in result [:query :reuse/type-key])
          :candidate-count (get-in result [:query :returned])
          :kernel-rechecked 1}
         :proofs
         {:foreign-declarations 1
          :distinct-normalized-statements 1
          :native-abstractions-reused 1
          :new-semantic-proof-objects
          ;; the mapping lands on a declaration that already existed, so this
          ;; stroke reused a native abstraction and created nothing new
          (accounting/new-proof-objects mappings {:reused #{native-id}})
          :mappings mappings
          :axioms {native-id axioms}
          :lean-proofs-visible-to-rainbow? false}
         :deferred {:search (count search-deferred)
                    :search-names (vec (sort search-deferred))}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mapping-count (count all-mappings)
          :all-mappings-id (canonical/content-id all-mappings)
          :new-mappings mappings}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :mathlib-day37/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day37/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command second-path]]
  (if (= "replay" command)
    (let [result (load-report (or second-path report-path))]
      (println (pr-str result))
      (when-not (= :replayed (:status result)) (System/exit 1)))
    (let [value (report (or command default-catalog-path)
                        (or second-path default-statement-path))]
      (println (pr-str value))
      (when-not (= :passed (:status value)) (System/exit 1)))))
