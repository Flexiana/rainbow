(ns rainbow.history.mathlib-logic-basic-exact
  "Exact-statement nativeization and synthesized Mathlib Logic.Basic proofs."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-logic-basic :as mathlib-logic-basic]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(def report-path "artifacts/day33/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day33-candidates.edn")
(def source-path "Mathlib/Logic/Basic.lean")

(def proof-search-budget
  {:states 1000 :depth 64 :wall-ms 10000
   :local-application-depth 4 :local-application-terms 128})

(def constant-aliases
  ;; Historical reports pin the concept boundary available in their stroke.
  (dissoc mathlib-native/default-constant-aliases
          "Iff.intro" "Iff.mp" "Iff.mpr"))

;; These are exact proof-redacted exporter records, not hand-nativeized types.
;; Keeping the two promoted statements here makes their independent Rainbow
;; proofs reproducible without requiring a local Mathlib checkout during tests.
(def promoted-statements
  [{:rainbow.catalog/kind :statement
    :foreign/name "exists_prop_of_false"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes []
    :foreign/type-fingerprint "lean-hash64:2884395783"
    :foreign/type
    [:pi [:sort [:zero]]
     [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
      [:pi [:app [:const "Not" []] [:bound 1]]
       [:app [:const "Not" []]
        [:app [:app [:const "Exists" [[:zero]]] [:bound 2]]
         [:lam [:bound 2] [:app [:bound 2] [:bound 0]] :explicit]]]
       :explicit]
      :implicit]
     :implicit]
    :foreign/value :redacted
    :foreign/location nil}

   {:rainbow.catalog/kind :statement
    :foreign/name "Iff.not"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes []
    :foreign/type-fingerprint "lean-hash64:3643782670"
    :foreign/type
    [:pi [:sort [:zero]]
     [:pi [:sort [:zero]]
      [:pi [:app [:app [:const "Iff" []] [:bound 1]] [:bound 0]]
       [:app
        [:app [:const "Iff" []]
         [:app [:const "Not" []] [:bound 2]]]
        [:app [:const "Not" []] [:bound 1]]]
       :explicit]
      :implicit]
     :implicit]
    :foreign/value :redacted
    :foreign/location nil}])

(def promoted-aliases
  {"exists_prop_of_false" 'logic/no-dependent-witness-without-carrier
   "Iff.not" 'logic/negation-congruence})

(def promoted-foreign-names (set (keys promoted-aliases)))

(def requested-foreign-names
  #{"Not.imp_symm" "not_imp_self" "not_imp_not" "Iff.not_right"
    "Iff.not" "Iff.not_left" "iff_not_comm" "not_iff" "not_iff_comm"
    "not_iff_not" "not_imp_comm" "not_and_not_right"
    "not_imp_self._simp_1" "forall_true_iff._simp_1"
    "forall_true_left._simp_1" "Prop.forall_iff" "exists_prop_of_false"
    "and_or_imp" "forall_true_iff'" "or_congr_right'" "or_congr_left'"
    "forall_or_left" "forall_or_right" "and_symm_right" "and_symm_left"
    "forall₂_or_left" "forall_prop_congr" "forall_prop_congr'"
    "eq_true_intro" "eq_false_intro" "imp_iff_right_iff" "Iff.iff"
    "eq_iff_eq_cancel_left" "eq_iff_eq_cancel_right"})

(def nativeization-deferred-foreign-names
  #{"forall_prop_congr" "forall_prop_congr'"})

(def search-deferred-foreign-names
  (set/difference requested-foreign-names
                  promoted-foreign-names
                  nativeization-deferred-foreign-names))

(defn- prove-statement [checked-environment statement]
  (let [nativeized
        (mathlib-native/nativeize-statement-type
         checked-environment statement {:constant-aliases constant-aliases})]
    (when-not (= :nativeized (:status nativeized))
      (throw (ex-info "Promoted Mathlib statement did not nativeize"
                      {:statement (:foreign/name statement)
                       :result nativeized})))
    (let [started (proof/start checked-environment (:type nativeized)
                               {:universes (:universes nativeized)})
          proved (when (= :ready (:status started))
                   (search/prove (:state started) proof-search-budget))]
      (when-not (and (= :proved (:status proved))
                     (= :checked (get-in proved [:kernel :status])))
        (throw (ex-info "Promoted Mathlib statement was not synthesized"
                        {:statement (:foreign/name statement)
                         :started started :result proved})))
      {:nativeized nativeized :proof proved})))

(defn build []
  (reduce
   (fn [{:keys [environment results] :as state} statement]
     (let [{:keys [nativeized proof]} (prove-statement environment statement)
           foreign-name (:foreign/name statement)
           candidate
           {:rainbow/kind :theorem
            :rainbow/aliases #{(get promoted-aliases foreign-name)}
            :rainbow/universes (:universes nativeized)
            :rainbow/type (:type nativeized)
            :rainbow/value (get-in proof [:proof :proof/term])
            :rainbow/transparency :opaque
            :rainbow/dependencies
            (into (term/constants (:type nativeized))
                  (term/constants (get-in proof [:proof :proof/term])))
            :rainbow/provenance
            {:origin :native :producer :exact-statement-proof-search
             :foreign/system :lean :foreign/library :mathlib
             :foreign/version mathlib/pinned-version
             :foreign/commit mathlib/pinned-commit
             :foreign/source source-path
             :foreign/name foreign-name
             :foreign/type-fingerprint (:foreign/type-fingerprint statement)
             :foreign/proof-hidden? true}
            :rainbow/schema-version 1}
           added (kernel/add-declaration environment candidate)]
       (when-not (= :accepted (:status added))
         (throw (ex-info "Synthesized Mathlib theorem was kernel rejected"
                         {:statement foreign-name :result added})))
       (assoc state
              :environment (:environment added)
              :results (conj results
                             {:statement statement
                              :nativeized nativeized
                              :proof proof
                              :declaration (:declaration added)}))))
   (let [prior (mathlib-logic-basic/build)]
     {:environment (:environment prior) :prior prior :results []})
   promoted-statements))

(defn result-mappings [results]
  (mapv (fn [{:keys [statement declaration]}]
          {:foreign/name (:foreign/name statement)
           :native/id (:rainbow/id declaration)})
        results))

(defn all-mappings [{:keys [prior results]}]
  (vec (concat (mathlib-logic-basic/all-mappings prior) (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        prior-environment (:environment (mathlib-logic-basic/build))
        nativeization-results
        (mapv #(mathlib-native/nativeize-statement-type
                prior-environment % {:constant-aliases constant-aliases})
              (:statements batch))
        nativeized (filter #(= :nativeized (:status %)) nativeization-results)
        rejected (filter #(= :rejected (:status %)) nativeization-results)
        {:keys [environment prior results] :as built} (build)
        mappings (result-mappings results)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-ids (mapv :native/id mappings)
        axioms (into {}
                     (map (fn [id] [id (kernel/axioms environment id)]))
                     native-ids)
        generated-telemetry
        (mapv (fn [{:keys [statement proof]}]
                {:foreign/name (:foreign/name statement)
                 :states-created (get-in proof [:telemetry :states-created])
                 :local-application-candidates
                 (get-in proof [:telemetry :local-application-candidates])
                 :kernel-status (get-in proof [:kernel :status])})
              results)
        rejected-names (set (map :foreign/name rejected))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names
                (set (map :foreign/name (:statements batch))))
             (= 34 (count requested-foreign-names))
             (= 32 (count nativeized))
             (= nativeization-deferred-foreign-names rejected-names)
             (= 2 (count mappings) (count results)
                (count (distinct native-ids)))
             (= promoted-foreign-names (set (map :foreign/name mappings)))
             (= 69 (count proved-names) (:proved summary))
             (= mathlib/pinned-distinct-theorem-count (:theorems summary))
             (every? empty? (vals axioms))
             (every? #(= :checked (:kernel-status %)) generated-telemetry)
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :path source-path}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested (count requested-foreign-names)
          :proof-values :redacted}
         :nativeization
         {:nativeized (count nativeized)
          :rejected (count rejected)
          :explicit-concept-map constant-aliases
          :rejected-statements
          (mapv (fn [result]
                  {:foreign/name (:foreign/name result)
                   :reason (get-in result [:error :error/category])
                   :unresolved (get-in result [:error :foreign/name])})
                rejected)}
         :proofs
         {:generated (count mappings) :mappings mappings
          :telemetry generated-telemetry :axioms axioms
          :lean-proofs-visible-to-rainbow? false
          :theorem-reuse-enabled? false}
         :deferred
         {:nativeization
          (mapv (fn [name]
                  {:foreign/name name :reason :missing-native-iff-eliminator})
                (sort nativeization-deferred-foreign-names))
          :search
          (mapv (fn [name]
                  {:foreign/name name :reason :bounded-search-not-proved})
                (sort search-deferred-foreign-names))}
         :measured-capability-growth
         {:regression-batch
          {:statements 31 :before-dependent-prefix-search 5
           :after-dependent-prefix-search 14}
          :fresh-batch
          {:statements 34 :nativeized 32 :proved 2 :search-deferred 30
           :nativeization-deferred 2}
          :search-feature :kernel-inferred-dependent-local-application-prefixes
          :manual-type-transcription-removed? true}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings all-mappings}
         :trusted-base-change :none
         :prior-proof-count (count (mathlib-logic-basic/all-mappings prior))}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :mathlib-day33/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day33/report-read-failed
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
