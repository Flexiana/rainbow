(ns rainbow.history.mathlib-adaptive-exact
  "Adaptive exact-statement proving with native connective focusing."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-logic-basic-exact :as mathlib-logic-basic-exact]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(def report-path "artifacts/day34/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day34-candidates.edn")

(def baseline-budget
  {:states 2000 :depth 96 :wall-ms 5000
   :local-application-depth 4 :local-application-terms 128})

(def focused-budget
  {:states 3000 :depth 128 :wall-ms 5000
   :local-application-depth 4 :local-application-terms 128
   :local-application-compositional? true
   :native-logic-focus? true :native-logic-prune? true})

(def constant-aliases
  ;; Preserve the exact native concept boundary measured by the Day 34 report.
  (dissoc mathlib-native/default-constant-aliases
          "Ne" "ExistsUnique" "ExistsUnique.elim" "ExistsUnique.intro"
          "Function.Bijective" "Function.Injective" "Function.Involutive"
          "Function.Surjective"))

(def selected-foreign-names
  ["Bool.involutive_not" "Fact.elim" "instCommutativeXor"
   "Function.not_involutive" "em" "em'" "fact_iff"
   "instDecidableFact._proof_1" "of_not_not" "or_not" "peirce"
   "Classical.by_contradiction" "by_contra" "by_contradiction"
   "of_not_imp" "Function.mtr" "Not.imp_symm" "eq_equivalence"
   "not_imp_self" "Function.not_bijective" "Function.not_injective"
   "Function.not_surjective" "Classical.by_cases" "by_cases"
   "existsUnique_false" "Classical.byContradiction'._proof_1"
   "eq_true_intro" "not_or_of_imp" "or_not_of_imp" "xor_true"
   "Xor'.or" "Xor.or" "forall_true_iff._simp_1" "forall_true_left"
   "not_imp_not" "not_imp_self._simp_1" "xor_self" "Iff.not_right"
   "eq_false_intro" "imp_iff_not_or" "imp_iff_or_not"
   "imp_iff_right_iff" "not_imp_comm" "Classical.prop_complete"
   "Iff.not_left" "iff_not_comm" "imp_and_neg_imp_iff"
   "not_and_not_right" "not_iff" "not_iff_comm" "not_iff_not"
   "not_imp" "not_xor" "xor_false" "xor_iff_iff_not"
   "xor_iff_not_iff" "xor_iff_not_iff'" "xor_not_left"
   "xor_not_right" "forall_true_left._simp_1" "iff_comm_eq"
   "iff_eq_eq" "xor_comm" "xor_not_not" "existsUnique_prop"
   "Exists.snd" "Prop.forall_iff" "imp_or"
   "existsUnique_false._simp_1" "and_iff_not_or_not" "not_and_or"
   "or_iff_not_and_not" "existsUnique_prop_of_true" "and_or_imp"
   "imp_or'" "not_xor._simp_1" "xor_not_left._simp_1"
   "xor_not_right._simp_1" "Function.FactorsThrough.rfl" "eq_or_ne"
   "exists_or_forall_not" "forall_or_exists_not"
   "forall_or_of_or_forall" "forall_true_iff'"
   "iff_mpr_iff_true_intro" "imp_congr_eq" "ne_or_eq"
   "or_congr_right'" "Function.cantor_surjective" "forall_or_left"
   "forall_or_right" "iff_iff_and_or_not_and_not"
   "iff_iff_not_or_and_or_not" "not_forall_not" "or_congr_left'"
   "xor_iff_or_and_not_and" "Function.cantor_injective"
   "Prop.exists_iff" "eq_comm_eq" "not_ne_iff" "xor_def"
   "ExistsUnique.exists" "Iff.iff" "eq_iff_eq_cancel_left"
   "Ne.ne_or_ne" "eq_iff_eq_cancel_right" "exists_apply_eq_apply'"
   "Function.Surjective.hasRightInverse" "cast_bijective"
   "eq_mp_bijective" "eq_mpr_bijective" "Xor.eq_1" "and_symm_right"
   "exists_apply_eq" "imp_congr_ctx_eq" "existsUnique_eq'._simp_1"
   "existsUnique_eq._simp_1" "Function.surjective_iff_hasRightInverse"
   "Eq.trans_ne" "Ne.trans_eq" "and_symm_left" "ne_of_eq_of_ne"
   "ne_of_ne_of_eq" "Function.not_surjective_Type"
   "Function.symmetric_apply_eq_iff" "and_forall_ne"
   "exists_of_exists_mem" "forall_and_index"])

(def requested-foreign-names (set selected-foreign-names))

;; Exact proof-redacted exporter records for the four promoted results.
(def promoted-statements
  [{:rainbow.catalog/kind :statement
    :foreign/name "exists_apply_eq_apply'"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes ["u_1" "u_2"]
    :foreign/type-fingerprint "lean-hash64:1480871514"
    :foreign/type
    [:pi [:sort [:param "u_1"]]
     [:pi [:sort [:param "u_2"]]
      [:pi [:pi [:bound 1] [:bound 1] :explicit]
       [:pi [:bound 2]
        [:app [:app [:const "Exists" [[:param "u_1"]]] [:bound 3]]
         [:lam [:bound 3]
          [:app [:app [:app [:const "Eq" [[:param "u_2"]]] [:bound 3]]
                 [:app [:bound 2] [:bound 1]]]
           [:app [:bound 2] [:bound 0]]]
          :explicit]]
        :explicit]
       :explicit]
      :implicit]
     :implicit]
    :foreign/value :redacted :foreign/location nil}

   {:rainbow.catalog/kind :statement
    :foreign/name "forall_or_of_or_forall"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes ["u_3"]
    :foreign/type-fingerprint "lean-hash64:4275673901"
    :foreign/type
    [:pi [:sort [:param "u_3"]]
     [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
      [:pi [:sort [:zero]]
       [:pi [:app [:app [:const "Or" []] [:bound 0]]
             [:pi [:bound 2] [:app [:bound 2] [:bound 0]] :explicit]]
        [:pi [:bound 3]
         [:app [:app [:const "Or" []] [:bound 2]]
          [:app [:bound 3] [:bound 0]]]
         :explicit]
        :explicit]
       :implicit]
      :implicit]
     :implicit]
    :foreign/value :redacted :foreign/location nil}

   {:rainbow.catalog/kind :statement
    :foreign/name "exists_of_exists_mem"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes ["u_1"]
    :foreign/type-fingerprint "lean-hash64:1685146627"
    :foreign/type
    [:pi [:sort [:param "u_1"]]
     [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
      [:pi [:pi [:bound 1] [:sort [:zero]] :explicit]
       [:pi
        [:app [:app [:const "Exists" [[:param "u_1"]]] [:bound 2]]
         [:lam [:bound 2]
          [:app [:app [:const "Exists" [[:zero]]]
                 [:app [:bound 2] [:bound 0]]]
           [:lam [:app [:bound 2] [:bound 0]]
            [:app [:bound 2] [:bound 1]] :explicit]]
          :explicit]]
        [:app [:app [:const "Exists" [[:param "u_1"]]] [:bound 3]]
         [:lam [:bound 3] [:app [:bound 2] [:bound 0]] :explicit]]
        :explicit]
       :implicit]
      :implicit]
     :implicit]
    :foreign/value :redacted :foreign/location nil}

   {:rainbow.catalog/kind :statement
    :foreign/name "forall_true_iff'"
    :foreign/module "Mathlib.Logic.Basic"
    :foreign/universes ["u_1"]
    :foreign/type-fingerprint "lean-hash64:2422482048"
    :foreign/type
    [:pi [:sort [:param "u_1"]]
     [:pi [:pi [:bound 0] [:sort [:zero]] :explicit]
      [:pi
       [:pi [:bound 1]
        [:app [:app [:const "Iff" []] [:app [:bound 1] [:bound 0]]]
         [:const "True" []]]
        :explicit]
       [:app [:app [:const "Iff" []]
              [:pi [:bound 2] [:app [:bound 2] [:bound 0]] :explicit]]
        [:const "True" []]]
       :explicit]
      :implicit]
     :implicit]
    :foreign/value :redacted :foreign/location nil}])

(def promoted-aliases
  {"exists_apply_eq_apply'" 'function/equal-image-has-preimage
   "forall_or_of_or_forall" 'logic/disjunction-lifts-over-forall
   "exists_of_exists_mem" 'logic/existence-forget-refinement
   "forall_true_iff'" 'logic/forall-equivalent-truth})

(def promoted-foreign-names (set (keys promoted-aliases)))

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
      (throw (ex-info "Promoted Day 34 statement did not nativeize"
                      {:statement (:foreign/name statement)
                       :result nativeized})))
    (let [{:keys [portfolio result]} (try-search checked-environment nativeized)]
      (when-not (and (= :proved (:status result))
                     (= :checked (get-in result [:kernel :status])))
        (throw (ex-info "Promoted Day 34 statement was not synthesized"
                        {:statement (:foreign/name statement)
                         :portfolio portfolio :result result})))
      {:nativeized nativeized :portfolio portfolio :proof result})))

(defn build []
  (reduce
   (fn [{:keys [environment results] :as state} statement]
     (let [{:keys [nativeized portfolio proof]}
           (prove-statement environment statement)
           foreign-name (:foreign/name statement)
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
         (throw (ex-info "Day 34 synthesized theorem was kernel rejected"
                         {:statement foreign-name :result added})))
       (assoc state :environment (:environment added)
              :results (conj results
                             {:statement statement :nativeized nativeized
                              :portfolio portfolio :proof proof
                              :declaration (:declaration added)}))))
   (let [prior (mathlib-logic-basic-exact/build)]
     {:environment (:environment prior) :prior prior :results []})
   promoted-statements))

(defn result-mappings [results]
  (mapv (fn [{:keys [statement declaration]}]
          {:foreign/name (:foreign/name statement)
           :native/id (:rainbow/id declaration)})
        results))

(defn all-mappings [{:keys [prior results]}]
  (vec (concat (mathlib-logic-basic-exact/all-mappings prior) (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        prior-environment (:environment (mathlib-logic-basic-exact/build))
        nativeization-results
        (mapv #(mathlib-native/nativeize-statement-type
                prior-environment % {:constant-aliases constant-aliases})
              (:statements batch))
        nativeized (filter #(= :nativeized (:status %)) nativeization-results)
        rejected (filter #(= :rejected (:status %)) nativeization-results)
        rejected-names (set (map :foreign/name rejected))
        search-deferred
        (set/difference requested-foreign-names rejected-names
                        promoted-foreign-names)
        {:keys [environment results] :as built} (build)
        mappings (result-mappings results)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-ids (mapv :native/id mappings)
        axioms (into {} (map (fn [id] [id (kernel/axioms environment id)]))
                     native-ids)
        telemetry
        (mapv (fn [{:keys [statement portfolio proof]}]
                {:foreign/name (:foreign/name statement)
                 :portfolio portfolio
                 :states-created (get-in proof [:telemetry :states-created])
                 :local-application-candidates
                 (get-in proof [:telemetry :local-application-candidates])
                 :native-logic-candidates
                 (get-in proof [:telemetry :native-logic-candidates])
                 :kernel-status (get-in proof [:kernel :status])})
              results)
        unresolved-counts
        (into (sorted-map)
              (frequencies (keep #(get-in % [:error :foreign/name]) rejected)))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names
                (set (map :foreign/name (:statements batch))))
             (= 128 (count requested-foreign-names))
             (= 71 (count nativeized)) (= 57 (count rejected))
             (= 67 (count search-deferred))
             (= 4 (count mappings) (count results)
                (count (distinct native-ids)))
             (= promoted-foreign-names (set (map :foreign/name mappings)))
             (= 73 (count proved-names) (:proved summary))
             (= mathlib/pinned-distinct-theorem-count (:theorems summary))
             (every? empty? (vals axioms))
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
          :unresolved-constant-counts unresolved-counts
          :iff-eliminators
          {"Iff.intro" 'proposition/equivalence-intro
           "Iff.mp" 'proposition/equivalence-forward
           "Iff.mpr" 'proposition/equivalence-backward}}
         :proofs
         {:generated (count mappings) :mappings mappings
          :telemetry telemetry :axioms axioms
          :lean-proofs-visible-to-rainbow? false
          :theorem-reuse-enabled? false}
         :deferred
         {:nativeization (count rejected-names)
          :search (count search-deferred)
          :search-names (vec (sort search-deferred))}
         :measured-capability-growth
         {:unchanged-day33-batch
          {:nativeized-before 32 :nativeized-after 34
           :direct-iff-not-states-before 87
           :focused-compositional-states-after 18}
          :wide-stroke
          {:selected 128 :nativeized 71 :promoted 4
           :search-deferred 67 :nativeization-deferred 57}
          :portfolio [:short-baseline :focused-compositional-fallback]
          :long-timeout-probe-promotions 0}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings all-mappings}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :mathlib-day34/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day34/report-read-failed
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
