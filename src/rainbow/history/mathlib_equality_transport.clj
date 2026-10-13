(ns rainbow.history.mathlib-equality-transport
  "Focused equality transport over exact proof-redacted Mathlib statements."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-adaptive-exact :as mathlib-adaptive-exact]
            [rainbow.history.mathlib-unique-existence-exact :as mathlib-unique-existence-exact]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(def report-path "artifacts/day36/report.edn")
(def default-catalog-path mathlib-unique-existence-exact/default-catalog-path)
(def default-statement-path mathlib-unique-existence-exact/default-statement-path)
(def requested-foreign-names mathlib-unique-existence-exact/requested-foreign-names)
(def constant-aliases mathlib-unique-existence-exact/constant-aliases)

(def baseline-budget mathlib-unique-existence-exact/baseline-budget)

(def focused-budget
  (assoc mathlib-unique-existence-exact/focused-budget
         :wall-ms 5000
         :native-equality-rewrite? true))

(def promoted-specs
  [{:foreign/names ["ne_of_eq_of_ne" "Eq.trans_ne"]
    :native/alias 'logic/equality-left-preserves-inequality
    :statement
    {:rainbow.catalog/kind :statement
     :foreign/name "ne_of_eq_of_ne"
     :foreign/module "Mathlib.Logic.Basic"
     :foreign/universes ["u_1"]
     :foreign/type-fingerprint "lean-hash64:315787734"
     :foreign/type
     [:pi [:sort [:param "u_1"]]
      [:pi [:bound 0]
       [:pi [:bound 1]
        [:pi [:bound 2]
         [:pi
          [:app [:app [:app [:const "Eq" [[:param "u_1"]]] [:bound 3]]
                 [:bound 2]] [:bound 1]]
          [:pi
           [:app [:app [:app [:const "Ne" [[:param "u_1"]]] [:bound 4]]
                  [:bound 2]] [:bound 1]]
           [:app [:app [:app [:const "Ne" [[:param "u_1"]]] [:bound 5]]
                  [:bound 4]] [:bound 2]]
           :explicit]
          :explicit]
         :implicit]
        :implicit]
       :implicit]
      :implicit]
     :foreign/value :redacted :foreign/location nil}}

   {:foreign/names ["ne_of_ne_of_eq" "Ne.trans_eq"]
    :native/alias 'logic/equality-right-preserves-inequality
    :statement
    {:rainbow.catalog/kind :statement
     :foreign/name "ne_of_ne_of_eq"
     :foreign/module "Mathlib.Logic.Basic"
     :foreign/universes ["u_1"]
     :foreign/type-fingerprint "lean-hash64:2239812555"
     :foreign/type
     [:pi [:sort [:param "u_1"]]
      [:pi [:bound 0]
       [:pi [:bound 1]
        [:pi [:bound 2]
         [:pi
          [:app [:app [:app [:const "Ne" [[:param "u_1"]]] [:bound 3]]
                 [:bound 2]] [:bound 1]]
          [:pi
           [:app [:app [:app [:const "Eq" [[:param "u_1"]]] [:bound 4]]
                  [:bound 2]] [:bound 1]]
           [:app [:app [:app [:const "Ne" [[:param "u_1"]]] [:bound 5]]
                  [:bound 4]] [:bound 2]]
           :explicit]
          :explicit]
         :implicit]
        :implicit]
       :implicit]
      :implicit]
     :foreign/value :redacted :foreign/location nil}}

   {:foreign/names ["imp_congr_eq"]
    :native/alias 'logic/implication-congruence-from-proposition-equality
    :statement
    {:rainbow.catalog/kind :statement
     :foreign/name "imp_congr_eq"
     :foreign/module "Mathlib.Logic.Basic"
     :foreign/universes []
     :foreign/type-fingerprint "lean-hash64:1992560319"
     :foreign/type
     [:pi [:sort [:zero]]
      [:pi [:sort [:zero]]
       [:pi [:sort [:zero]]
        [:pi [:sort [:zero]]
         [:pi
          [:app [:app [:app [:const "Eq" [[:succ [:zero]]]]
                       [:sort [:zero]]] [:bound 3]] [:bound 1]]
          [:pi
           [:app [:app [:app [:const "Eq" [[:succ [:zero]]]]
                        [:sort [:zero]]] [:bound 3]] [:bound 1]]
           [:app
            [:app
             [:app [:const "Eq" [[:succ [:zero]]]] [:sort [:zero]]]
             [:pi [:bound 5] [:bound 5] :explicit]]
            [:pi [:bound 3] [:bound 3] :explicit]]
           :explicit]
          :explicit]
         :implicit]
        :implicit]
       :implicit]
      :implicit]
     :foreign/value :redacted :foreign/location nil}}])

(def promoted-foreign-names
  (set (mapcat :foreign/names promoted-specs)))

(defn- try-search [checked-environment nativeized]
  (let [start #(proof/start checked-environment (:type nativeized)
                            {:universes (:universes nativeized)})
        baseline (search/prove (:state (start)) baseline-budget)]
    (if (= :proved (:status baseline))
      {:portfolio :baseline :result baseline}
      {:portfolio :focused-equality
       :result (search/prove (:state (start)) focused-budget)})))

(defn- prove-spec [checked-environment {:keys [statement] :as spec}]
  (let [nativeized
        (mathlib-native/nativeize-statement-type
         checked-environment statement {:constant-aliases constant-aliases})]
    (when-not (= :nativeized (:status nativeized))
      (throw (ex-info "Promoted Day 36 statement did not nativeize"
                      {:statement (:foreign/name statement)
                       :result nativeized})))
    (let [{:keys [portfolio result]} (try-search checked-environment nativeized)]
      (when-not (and (= :proved (:status result))
                     (= :checked (get-in result [:kernel :status])))
        (throw (ex-info "Promoted Day 36 statement was not synthesized"
                        {:statement (:foreign/name statement)
                         :portfolio portfolio :result result})))
      {:spec spec :nativeized nativeized
       :portfolio portfolio :proof result})))

(defn- add-result [environment {:keys [spec nativeized proof] :as result}]
  (let [statement (:statement spec)
        proof-term (get-in proof [:proof :proof/term])
        added
        (kernel/add-declaration
         environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:native/alias spec)}
          :rainbow/universes (:universes nativeized)
          :rainbow/type (:type nativeized)
          :rainbow/value proof-term
          :rainbow/transparency :opaque
          :rainbow/dependencies
          (into (term/constants (:type nativeized))
                (term/constants proof-term))
          :rainbow/provenance
          {:origin :native :producer :focused-equality-exact-statement-search
           :foreign/system :lean :foreign/library :mathlib
           :foreign/version mathlib/pinned-version
           :foreign/commit mathlib/pinned-commit
           :foreign/module (:foreign/module statement)
           :foreign/names (:foreign/names spec)
           :foreign/type-fingerprint (:foreign/type-fingerprint statement)
           :foreign/proof-hidden? true}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status added))
      (throw (ex-info "Day 36 synthesized theorem was kernel rejected"
                      {:statement (:foreign/name statement) :result added})))
    [(:environment added) (assoc result :declaration (:declaration added))]))

(defn build []
  (let [prior (mathlib-unique-existence-exact/build)
        base-environment (:environment prior)
        ;; Prevent same-stroke theorem reuse: all three semantic claims are
        ;; synthesized before any Day 36 result is registered.
        synthesized (mapv #(prove-spec base-environment %) promoted-specs)
        [environment results]
        (reduce (fn [[environment results] result]
                  (let [[next-environment registered]
                        (add-result environment result)]
                    [next-environment (conj results registered)]))
                [base-environment []] synthesized)]
    {:environment environment :prior prior :base-environment base-environment
     :results results}))

(defn result-mappings [results]
  (vec
   (mapcat (fn [{:keys [spec declaration]}]
             (map (fn [foreign-name]
                    {:foreign/name foreign-name
                     :native/id (:rainbow/id declaration)})
                  (:foreign/names spec)))
           results)))

(defn all-mappings [{:keys [prior results]}]
  (vec (concat (mathlib-unique-existence-exact/all-mappings prior) (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        statements-by-name (into {} (map (juxt :foreign/name identity)
                                         (:statements batch)))
        coincident-groups
        (mapv (fn [{:keys [foreign/names]}]
                {:foreign/names names
                 :same-type?
                 (apply = (map (comp :foreign/type statements-by-name) names))
                 :same-fingerprint?
                 (apply = (map (comp :foreign/type-fingerprint
                                     statements-by-name) names))})
              (filter #(> (count (:foreign/names %)) 1) promoted-specs))
        {:keys [environment base-environment results] :as built} (build)
        nativeization-results
        (mapv #(mathlib-native/nativeize-statement-type
                base-environment % {:constant-aliases constant-aliases})
              (:statements batch))
        nativeized (filter #(= :nativeized (:status %)) nativeization-results)
        rejected (filter #(= :rejected (:status %)) nativeization-results)
        nativeized-names (set (map :foreign/name nativeized))
        prior-mappings (mathlib-unique-existence-exact/all-mappings (:prior built))
        prior-proved-names (set (map :foreign/name prior-mappings))
        already-proved (set/intersection nativeized-names prior-proved-names)
        search-deferred
        (set/difference nativeized-names prior-proved-names
                        promoted-foreign-names)
        mappings (result-mappings results)
        all-mappings (all-mappings built)
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        native-ids (vec (distinct (map :native/id mappings)))
        axioms (into {} (map (fn [id] [id (kernel/axioms environment id)]))
                     native-ids)
        telemetry
        (mapv (fn [{:keys [spec portfolio proof]}]
                {:foreign/names (:foreign/names spec)
                 :portfolio portfolio
                 :states-created (get-in proof [:telemetry :states-created])
                 :native-logic-candidates
                 (get-in proof [:telemetry :native-logic-candidates])
                 :rewrite-attempts
                 (count (filter #(= :rewrite (get-in % [:strategy :tactic]))
                                (:attempts proof)))
                 :kernel-status (get-in proof [:kernel :status])})
              results)
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names
                (set (map :foreign/name (:statements batch))))
             (= 128 (count requested-foreign-names))
             (= 91 (count nativeized)) (= 37 (count rejected))
             (= 6 (count already-proved))
             (= 80 (count search-deferred))
             (= 5 (count mappings)) (= 3 (count results) (count native-ids))
             (= promoted-foreign-names (set (map :foreign/name mappings)))
             (every? :same-type? coincident-groups)
             (every? :same-fingerprint? coincident-groups)
             (= 80 (count proved-names) (:proved summary))
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
         {:nativeized (count nativeized) :rejected (count rejected)}
         :proofs
         {:foreign-declarations (count mappings)
          :semantic-proofs (count results)
          :coincident-statement-groups coincident-groups
          :mappings mappings :telemetry telemetry :axioms axioms
          :lean-proofs-visible-to-rainbow? false
          :theorem-reuse-enabled? false}
         :deferred
         {:already-proved-in-stroke (count already-proved)
          :nativeization (count rejected)
          :search (count search-deferred)
          :search-names (vec (sort search-deferred))}
         :measured-capability-growth
         {:before
          {:inequality-transport-targets 4 :promotions 0
           :states-created [9 9 9 9]
           :native-logic-candidates [0 0 0 0]}
          :after
          {:inequality-transport-targets 4 :promotions 4
           :states-created [13 13 10 10]
           :additional-held-out-promotion "imp_congr_eq"}
          :parallel-wide-stroke
          {:unproved-nativeized-targets 85 :promotions 5
           :frontier-exhausted 52 :wall-budget 28}
          :stroke-policy
          {:shape :broad-short-adaptive
           :parallel? true :focused-equality-rewrite? true}}
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
         :error/category :mathlib-day36/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day36/report-read-failed
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
