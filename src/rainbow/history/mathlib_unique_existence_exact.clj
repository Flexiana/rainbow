(ns rainbow.history.mathlib-unique-existence-exact
  "Exact unique-existence proofs and reusable native function predicates."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-adaptive-exact :as mathlib-adaptive-exact]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function-predicate :as function-predicate]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(def report-path "artifacts/day35/report.edn")
(def default-catalog-path mathlib-adaptive-exact/default-catalog-path)
(def default-statement-path mathlib-adaptive-exact/default-statement-path)
(def requested-foreign-names mathlib-adaptive-exact/requested-foreign-names)

(def constant-names
  ;; Pin the exact Day 35 concept boundary against future translator growth.
  #{"And" "And.intro" "And.left" "And.right" "Eq" "Eq.refl"
    "Exists" "Exists.elim" "Exists.fst" "Exists.intro"
    "ExistsUnique" "ExistsUnique.elim" "ExistsUnique.intro"
    "False" "False.elim"
    "Function.Bijective" "Function.Injective" "Function.Involutive"
    "Function.Surjective"
    "Iff" "Iff.intro" "Iff.mp" "Iff.mpr" "Ne" "Not"
    "Or" "Or.elim" "Or.inl" "Or.inr" "True" "True.intro"})

(def constant-aliases
  (select-keys mathlib-native/default-constant-aliases constant-names))

(def promoted-statements
  [{:rainbow.catalog/kind :statement
    :foreign/name "existsUnique_false"
    :foreign/module "Mathlib.Logic.ExistsUnique"
    :foreign/universes ["u_1"]
    :foreign/type-fingerprint "lean-hash64:3583870472"
    :foreign/type
    [:pi [:sort [:param "u_1"]]
     [:app [:const "Not" []]
      [:app [:app [:const "ExistsUnique" [[:param "u_1"]]] [:bound 0]]
       [:lam [:bound 0] [:const "False" []] :explicit]]]
     :implicit]
    :foreign/value :redacted :foreign/location nil}

   {:rainbow.catalog/kind :statement
    :foreign/name "ExistsUnique.exists"
    :foreign/module "Mathlib.Logic.ExistsUnique"
    :foreign/universes ["u_1"]
    :foreign/type-fingerprint "lean-hash64:953348889"
    :foreign/type
    [:pi [:sort [:param "u_1"]]
     [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
      [:pi
       [:app [:app [:const "ExistsUnique" [[:param "u_1"]]] [:bound 1]]
        [:lam [:bound 1] [:app [:bound 1] [:bound 0]] :explicit]]
       [:app [:app [:const "Exists" [[:param "u_1"]]] [:bound 2]]
        [:lam [:bound 2] [:app [:bound 2] [:bound 0]] :explicit]]
       :explicit]
      :implicit]
     :implicit]
    :foreign/value :redacted :foreign/location nil}])

(def promoted-aliases
  {"existsUnique_false" 'logic/no-unique-false-witness
   "ExistsUnique.exists" 'logic/unique-existence-implies-existence})

(def promoted-foreign-names (set (keys promoted-aliases)))

(def baseline-budget
  {:states 2000 :depth 96 :wall-ms 500
   :local-application-depth 4 :local-application-terms 128})

(def focused-budget
  {:states 3000 :depth 128 :wall-ms 1500
   :local-application-depth 4 :local-application-terms 128
   :local-application-compositional? true
   :native-logic-focus? true :native-logic-prune? true})

(defn- try-search [checked-environment nativeized]
  (let [start #(proof/start checked-environment (:type nativeized)
                            {:universes (:universes nativeized)})
        baseline (search/prove (:state (start)) baseline-budget)]
    (if (= :proved (:status baseline))
      {:portfolio :baseline :result baseline}
      {:portfolio :focused
       :result (search/prove (:state (start)) focused-budget)})))

(defn- prove-statement [checked-environment statement]
  (let [nativeized
        (mathlib-native/nativeize-statement-type
         checked-environment statement {:constant-aliases constant-aliases})]
    (when-not (= :nativeized (:status nativeized))
      (throw (ex-info "Promoted Day 35 statement did not nativeize"
                      {:statement (:foreign/name statement)
                       :result nativeized})))
    (let [{:keys [portfolio result]} (try-search checked-environment nativeized)]
      (when-not (and (= :proved (:status result))
                     (= :checked (get-in result [:kernel :status])))
        (throw (ex-info "Promoted Day 35 statement was not synthesized"
                        {:statement (:foreign/name statement)
                         :portfolio portfolio :result result})))
      {:statement statement :nativeized nativeized
       :portfolio portfolio :proof result})))

(defn- add-result [environment {:keys [statement nativeized proof] :as result}]
  (let [foreign-name (:foreign/name statement)
        proof-term (get-in proof [:proof :proof/term])
        added
        (kernel/add-declaration
         environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(get promoted-aliases foreign-name)}
          :rainbow/universes (:universes nativeized)
          :rainbow/type (:type nativeized)
          :rainbow/value proof-term
          :rainbow/transparency :opaque
          :rainbow/dependencies
          (into (term/constants (:type nativeized))
                (term/constants proof-term))
          :rainbow/provenance
          {:origin :native :producer :adaptive-exact-statement-search
           :foreign/system :lean :foreign/library :mathlib
           :foreign/version mathlib/pinned-version
           :foreign/commit mathlib/pinned-commit
           :foreign/module (:foreign/module statement)
           :foreign/name foreign-name
           :foreign/type-fingerprint (:foreign/type-fingerprint statement)
           :foreign/proof-hidden? true}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status added))
      (throw (ex-info "Day 35 synthesized theorem was kernel rejected"
                      {:statement foreign-name :result added})))
    [(:environment added) (assoc result :declaration (:declaration added))]))

(defn build []
  (let [prior (mathlib-adaptive-exact/build)
        base-environment
        (function-predicate/extend-environment (:environment prior))
        ;; All statements are synthesized against the same environment: a
        ;; Day 35 result can never become proof-search input for its peers.
        synthesized (mapv #(prove-statement base-environment %)
                          promoted-statements)
        [environment results]
        (reduce (fn [[environment results] result]
                  (let [[next-environment registered]
                        (add-result environment result)]
                    [next-environment (conj results registered)]))
                [base-environment []] synthesized)]
    {:environment environment :prior prior :base-environment base-environment
     :results results}))

(defn result-mappings [results]
  (mapv (fn [{:keys [statement declaration]}]
          {:foreign/name (:foreign/name statement)
           :native/id (:rainbow/id declaration)})
        results))

(defn all-mappings [{:keys [prior results]}]
  (vec (concat (mathlib-adaptive-exact/all-mappings prior) (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        {:keys [environment base-environment results] :as built} (build)
        nativeization-results
        (mapv #(mathlib-native/nativeize-statement-type
                base-environment % {:constant-aliases constant-aliases})
              (:statements batch))
        nativeized (filter #(= :nativeized (:status %)) nativeization-results)
        rejected (filter #(= :rejected (:status %)) nativeization-results)
        rejected-names (set (map :foreign/name rejected))
        search-deferred
        (set/difference (set (map :foreign/name nativeized))
                        promoted-foreign-names)
        mappings (result-mappings results)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-ids (mapv :native/id mappings)
        axioms (into {} (map (fn [id] [id (kernel/axioms environment id)]))
                     native-ids)
        predicate-axioms
        (into {} (map (fn [name] [name (kernel/axioms environment name)]))
              (map :name function-predicate/predicate-specs))
        telemetry
        (mapv (fn [{:keys [statement portfolio proof]}]
                {:foreign/name (:foreign/name statement)
                 :portfolio portfolio
                 :states-created (get-in proof [:telemetry :states-created])
                 :local-application-candidates
                 (get-in proof [:telemetry :local-application-candidates])
                 :kernel-status (get-in proof [:kernel :status])})
              results)
        rejection-counts
        (into (sorted-map)
              (frequencies
               (map #(or (get-in % [:error :foreign/name])
                         (get-in % [:error :error/category]))
                    rejected)))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names
                (set (map :foreign/name (:statements batch))))
             (= 128 (count requested-foreign-names))
             (= 91 (count nativeized)) (= 37 (count rejected))
             (= 89 (count search-deferred))
             (= 2 (count mappings) (count results)
                (count (distinct native-ids)))
             (= promoted-foreign-names (set (map :foreign/name mappings)))
             (= 75 (count proved-names) (:proved summary))
             (= mathlib/pinned-distinct-theorem-count (:theorems summary))
             (every? empty? (vals axioms))
             (every? empty? (vals predicate-axioms))
             (every? #(= :checked (:kernel-status %)) telemetry)
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit
                  :modules (vec (sort (set (map :foreign/module
                                                (:statements batch)))))}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested 128
          :proof-values :redacted}
         :nativeization
         {:nativeized (count nativeized) :rejected (count rejected)
          :rejection-counts rejection-counts
          :new-native-concepts
          {"Ne" 'equality/inequality
           "ExistsUnique" 'proposition/unique-existence
           "Function.Injective" 'function/injective
           "Function.Surjective" 'function/surjective
           "Function.Involutive" 'function/involutive
           "Function.Bijective" 'function/bijective}}
         :proofs
         {:generated (count mappings) :mappings mappings
          :telemetry telemetry :axioms axioms
          :lean-proofs-visible-to-rainbow? false
          :theorem-reuse-enabled? false}
         :function-predicates
         {:definitions (mapv :name function-predicate/predicate-specs)
          :axioms predicate-axioms :transparency :reducible}
         :deferred
         {:nativeization (count rejected-names)
          :search (count search-deferred)
          :search-names (vec (sort search-deferred))
          :parallel-function-probe
          {:targets ["Function.not_bijective" "Function.not_injective"
                     "Function.not_involutive" "Function.not_surjective"]
           :promotions 0 :reason :frontier-exhausted}}
         :measured-capability-growth
         {:unchanged-wide-stroke
          {:selected 128 :day34-nativeized 71
           :inequality-and-unique-nativeized 87
           :function-predicate-nativeized 91
           :promoted 2 :search-deferred 89 :nativeization-deferred 37}
          :stroke-policy
          {:shape :broad-short-adaptive
           :parallel-research-lane :function-predicate-probe
           :fallback :focused-compositional}}
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
         :error/category :mathlib-day35/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day35/report-read-failed
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
