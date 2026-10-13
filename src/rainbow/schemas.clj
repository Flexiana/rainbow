(ns rainbow.schemas
  "Schemas for Rainbow core terms, declarations, runs, and persisted artifacts."
  (:require [rainbow.schema :as schema]
            [rainbow.term :as term]))

(def content-id [:predicate :content-id])

(def level-schema
  [:tagged-vector
   {:zero [:tuple [:literal :zero]]
    :param [:tuple [:literal :param] :symbol]
    :succ [:tuple [:literal :succ] [:ref :level]]
    :max [:tuple [:literal :max] [:ref :level] [:ref :level]]
    :imax [:tuple [:literal :imax] [:ref :level] [:ref :level]]}])

(def term-schema
  [:tagged-vector
   {:sort [:tuple [:literal :sort] [:ref :level]]
    :bound [:tuple [:literal :bound] :natural]
    :const [:tuple [:literal :const] content-id [:vector [:ref :level]]]
    :app [:tuple [:literal :app] [:ref :term] [:ref :term]]
    :lam [:tuple [:literal :lam] [:ref :term] [:ref :term]
          [:enum #{:explicit :implicit}]]
    :pi [:tuple [:literal :pi] [:ref :term] [:ref :term]
         [:enum #{:explicit :implicit}]]
    :let [:tuple [:literal :let] [:ref :term] [:ref :term] [:ref :term]]}])

(defn declaration-map [value-schema]
  [:map
   {:required
    {:rainbow/id content-id
     :rainbow/kind [:enum #{:axiom :definition :theorem}]
     :rainbow/aliases [:set :symbol]
     :rainbow/universes [:vector :symbol]
     :rainbow/type [:ref :term]
     :rainbow/value value-schema
     :rainbow/transparency [:enum #{:reducible :semireducible :opaque}]
     :rainbow/dependencies [:set content-id]
     :rainbow/axioms [:set content-id]
     :rainbow/schema-version [:literal 1]}
    :optional {:rainbow/provenance :map}
    :closed? false}])

(def declaration-schema
  [:tagged-map :rainbow/kind
   {:axiom (declaration-map [:literal nil])
    :definition (declaration-map [:ref :term])
    :theorem (declaration-map [:ref :term])}])

(declare block-type-ast?)

(defn- block-binding? [binding]
  (and (vector? binding)
       (= 2 (count binding))
       (symbol? (first binding))
       (block-type-ast? (second binding))))

(defn- block-type-ast?
  "Recognizes the persisted named AST for dependent inductive parameters and
  constructor fields. Scope, positivity, and typing are checked by the kernel
  when the block is added or replayed."
  [value]
  (and
   (vector? value)
   (case (first value)
     :self (= 1 (count value))
     :var (and (= 2 (count value)) (symbol? (second value)))
     :sort (and (= 2 (count value)) (term/level? (second value)))
     :const (and (= 3 (count value))
                 (or (string? (second value)) (symbol? (second value)))
                 (vector? (nth value 2))
                 (every? term/level? (nth value 2)))
     :app (and (<= 3 (count value))
               (every? block-type-ast? (rest value)))
     :pi (and (= 3 (count value))
              (vector? (second value))
              (every? block-binding? (second value))
              (block-type-ast? (nth value 2)))
     false)))

(def block-type-schema [:predicate :block-type-ast])

(def block-parameter-schema
  [:map
   {:required {:parameter/name :symbol
               :parameter/type [:ref :block-type]}
    :closed? true}])

(def block-field-schema
  [:map
   {:required
    {:field/name :symbol
     :field/type [:ref :block-type]}
    :closed? true}])

(def block-constructor-schema
  [:map
   {:required {:constructor/alias :symbol
               :constructor/fields [:vector [:ref :block-field]]}
    :closed? true}])

(def inductive-block-schema
  [:map
   {:required
    {:rainbow/id content-id
     :block/schema-version [:literal 1]
     :block/alias :symbol
     :block/universes [:vector :symbol]
     :block/parameters [:vector [:ref :block-parameter]]
     :block/sort-level [:ref :level]
     :block/constructors [:vector [:ref :block-constructor] {:min 1}]}
    :closed? true}])

(def artifact-entry-schema
  [:tagged-map :entry/kind
   {:declaration
    [:map {:required {:entry/kind [:literal :declaration]
                      :entry/value [:ref :declaration]}
           :closed? true}]
    :inductive-block
    [:map {:required {:entry/kind [:literal :inductive-block]
                      :entry/value [:ref :inductive-block]}
           :closed? true}]}])

(def environment-artifact-schema
  [:map
   {:required
    {:rainbow.artifact/schema-version [:literal 1]
     :rainbow.artifact/kind [:literal :checked-environment]
     :rainbow.artifact/environment-id content-id
     :rainbow.artifact/declarations [:vector [:ref :declaration]]}
    :optional
    {:rainbow.artifact/inductive-blocks [:vector [:ref :inductive-block]]
     :rainbow.artifact/entries [:vector [:ref :artifact-entry]]}
    :closed? true}])

(def attempt-schema
  [:map
   {:required
    {:rainbow/kind [:literal :proof-attempt]
     :attempt/schema-version [:literal 1]
     :goal/hash content-id
     :strategy
     [:map {:required {:tactic :keyword}
            :optional {:term [:ref :term]}
            :closed? true}]
     :result [:enum #{:success :progress :failure :no-progress}]
     :failure/category [:maybe :keyword]
     :cost [:map {:required {:elapsed-ms :natural} :closed? true}]
     :attempt/id content-id}
    :closed? true}])

(def run-record-schema
  [:map
   {:required
    {:rainbow/kind [:literal :proof-run]
     :run/schema-version [:literal 1]
     :job/id [:or :keyword :symbol :string]
     :outcome [:enum #{:proved :blocked :failure :rejected}]
     :proof/id [:maybe content-id]
     :attempts [:vector [:ref :attempt]]
     :telemetry :map
     :run/id content-id}
    :closed? true}])

(def compiler-artifact-schema
  [:map
   {:required
    {:artifact/id content-id
     :status [:literal :compiled]
     :compiler/version [:literal 1]
     :compiler/target [:literal :clojure-reference]
     :source/declaration-id content-id
     :source/environment-id content-id
     :source/check [:enum #{:kernel-checked :block-validated}]
     :semantics :map
     :assurance :map
     :erasure
     [:map {:required {:leading-type-arguments :natural
                       :runtime-arity :natural}
            :closed? true}]
     :dependencies :natural}
    :closed? true}])

(def compiler-report-schema
  [:map
   {:required
    {:cases :natural
     :agreements :natural
     :mismatches [:vector :map]
     :operations [:map-of :keyword :natural {}]
     :status [:enum #{:passed :failed}]
     :environment-id content-id
     :artifacts [:map-of :keyword [:ref :compiler-artifact] {:min 1}]
     :report/id content-id}
    :closed? true}])

(def order-schema
  [:map
   {:required {:order/id :string
               :capacity-use [:range :natural {:min 1}]
               :working-capital :natural
               :margin :integer
               :rejection-penalty :natural
               :promised? :boolean}
    :closed? true}])

(def order-request-schema
  [:map
   {:required {:capacity :natural
               :working-capital :natural
               :orders [:vector [:ref :order] {:max 64}]}
    :closed? true}])

(def decision-model-schema
  [:map
   {:required
    {:model/kind [:literal :order-acceptance]
     :model/version [:literal 1]
     :model/objective [:literal :maximize-net-margin]
     :model/constraints
     [:vector [:enum #{:capacity :working-capital :promises}] {:min 3 :max 3}]
     :model/tie-break [:literal :lexicographic-accepted-ids]
     :model/readable-max-orders [:range :natural {:min 1 :max 24}]
     :model/fast-max-state-cells [:range :natural {:min 1 :max 1000000}]}
    :closed? true}])

(def decision-assurance-schema
  [:map
   {:required
    {:assurance/version [:literal 1]
     :assurance/id content-id
     :claim [:literal :optimal-order-acceptance]
     :scope [:literal :one-validated-finite-request]
     :deduction :map
     :computation :map
     :arithmetic :map
     :numerics :map
     :solver :map}
    :closed? true}])

(def decision-compiler-artifact-schema
  [:map
   {:required
    {:artifact/id content-id
     :status [:literal :compiled]
     :compiler/version [:literal 1]
     :compiler/target [:enum #{:clojure-readable :clojure-fast}]
     :model/id content-id
     :model [:ref :decision-model]
     :source :string
     :algorithm [:enum #{:exhaustive-enumeration
                         :two-resource-dynamic-program}]
     :semantics :map
     :assurance [:ref :decision-assurance]
     :evidence :map}
    :closed? true}])

(def decision-result-schema
  [:map
   {:required
    {:status [:enum #{:optimal :infeasible}]
     :decision/id content-id
     :accepted-ids [:vector :string]
     :rejected-ids [:vector :string]
     :objective :integer
     :totals :map
     :feasibility :map
     :contracts :map
     :optimality :map
     :explanation :map
     :assurance [:ref :decision-assurance]
     :telemetry :map}
    :closed? true}])

(def decision-report-schema
  [:map
   {:required
    {:status [:literal :passed]
     :report/id content-id
     :model/id content-id
     :input-schema :map
     :artifacts [:map-of :keyword [:ref :decision-compiler-artifact]
                 {:min 2 :max 2}]
     :artifact-issues [:map-of :keyword [:vector :map] {:min 2 :max 2}]
     :small-exhaustive :map
     :larger-solver-comparison :map
     :performance :map
     :generated-service :map
     :sample-decision [:ref :decision-result]
     :claim-boundaries :map
     :proof-capacity :map
     :trusted-base-lines :natural}
    :closed? true}])

(def proof-job-context-schema
  [:map
   {:required {:definitions [:vector content-id]
               :assumptions [:vector content-id]
               :concepts [:set :keyword]}
    :optional {:failed-attempt-keys [:set content-id]}
    :closed? true}])

(def proof-job-policy-schema
  [:map
   {:required
    {:allowed-axioms [:set content-id]
     :allowed-sources [:set [:enum #{:rainbow/native :lean/verified}]]
     :invent-lemmas? :boolean
     :generalize? :boolean
     :transport? :boolean
     :allow-definition-invention? :boolean}
    :closed? true}])

(def proof-job-budget-schema
  [:map
   {:required {:wall-ms [:range :natural {:min 1}]
               :states [:range :natural {:min 1}]
               :memory-mb [:range :natural {:min 1}]
               :candidate-lemmas :natural
               :llm-calls [:range :natural {:min 1}]}
    :closed? true}])

(def proof-job-request-schema
  [:map
   {:required
    {:job/id [:or :keyword :symbol :string]
     :job/version [:literal 1]
     :goal [:ref :term]
     :context [:ref :proof-job-context]
     :policy [:ref :proof-job-policy]
     :budget [:ref :proof-job-budget]
     :objective [:vector
                 [:enum #{:solve :minimize-assumptions
                          :maximize-reusable-lemmas :minimize-proof-size}]
                 {:min 1}]
     :return [:vector
              [:enum #{:proof :invented-lemmas :alternatives
                       :compressed-blockers :telemetry}]
              {:min 1}]}
    :closed? true}])

(def proof-job-response-schema
  [:tagged-map :status
   {:proved
    [:map
     {:required {:status [:literal :proved]
                 :job/id [:or :keyword :symbol :string]
                 :job/version [:literal 1]
                 :goal-hash content-id
                 :proof-hash content-id
                 :kernel :map
                 :invented-lemmas [:vector :map]
                 :alternatives [:vector :map]
                 :compressed-blockers [:vector :map]
                 :telemetry :map
                 :stroke :map
                 :response/id content-id}
      :optional {:proof :map}
      :closed? true}]
    :blocked
    [:map
     {:required {:status [:literal :blocked]
                 :job/id [:or :keyword :symbol :string]
                 :job/version [:literal 1]
                 :goal-hash content-id
                 :proved-subgoals [:vector content-id]
                 :compressed-blockers [:vector :map]
                 :dominant-failures [:vector :map]
                 :do-not-repeat [:vector content-id]
                 :telemetry :map
                 :stroke :map
                 :response/id content-id}
      :closed? true}]
    :rejected
    [:map
     {:required {:status [:literal :rejected]
                 :job/id [:or :keyword :symbol :string]
                 :job/version [:literal 1]
                 :error :map}
      :closed? true}]}])

(def extension-origin-schema
  [:map
   {:required {:kind [:literal :ai-generated]
               :model :string
               :run-id :string
               :source-hash content-id}
    :closed? true}])

(def extension-resource-schema
  [:map
   {:required {:wall-ms [:range :natural {:min 1}]
               :cpu-ms [:range :natural {:min 1}]
               :memory-mb [:range :natural {:min 16}]}
    :closed? true}])

(def extension-rollback-schema
  [:map
   {:required {:feature-flag :keyword
               :default-enabled? :boolean}
    :closed? true}])

(def extension-manifest-schema
  [:map
   {:required
    {:extension/id :keyword
     :extension/kind
     [:enum #{:tactic :retriever :search-policy :goal-normalizer
              :lemma-generator :critic :nativeization-adapter :transport
              :compiler-pass :solver-adapter :elaborator-rule}]
     :extension/version [:range :natural {:min 1}]
     :entry-point :symbol
     :capabilities [:set
                    [:enum #{:read-proof-state :emit-candidate-term
                             :emit-tactic-program}]
                    {:min 1}]
     :soundness-boundary [:literal :kernel-checks-output]
     :applicability [:set :keyword {:min 1}]
     :deterministic-seed? :boolean
     :origin [:ref :extension-origin]
     :resources [:ref :extension-resource]
     :evaluation [:map
                  {:required {:training-run [:maybe content-id]
                              :held-out-run [:maybe content-id]}
                   :closed? true}]
     :rollback [:ref :extension-rollback]}
    :closed? true}])

(def registry
  {:level level-schema
   :term term-schema
   :declaration declaration-schema
   :block-type block-type-schema
   :block-parameter block-parameter-schema
   :block-field block-field-schema
   :block-constructor block-constructor-schema
   :inductive-block inductive-block-schema
   :artifact-entry artifact-entry-schema
   :attempt attempt-schema
   :compiler-artifact compiler-artifact-schema
   :order order-schema
   :order-request order-request-schema
   :decision-model decision-model-schema
   :decision-assurance decision-assurance-schema
   :decision-compiler-artifact decision-compiler-artifact-schema
   :decision-result decision-result-schema
   :decision-report decision-report-schema
   :proof-job-context proof-job-context-schema
   :proof-job-policy proof-job-policy-schema
   :proof-job-budget proof-job-budget-schema
   :extension-origin extension-origin-schema
   :extension-resource extension-resource-schema
   :extension-rollback extension-rollback-schema})

(def predicates
  {:content-id #(and (string? %)
                     (boolean (re-matches #"sha256:[0-9a-f]{64}" %)))
   :block-type-ast block-type-ast?})

(def options {:registry registry :predicates predicates})

(defn explain-term [value]
  (schema/explain [:ref :term] value options))

(defn explain-declaration [value]
  (schema/explain [:ref :declaration] value options))

(defn explain-environment-artifact [value]
  (schema/explain environment-artifact-schema value options))

(defn explain-run-record [value]
  (schema/explain run-record-schema value options))

(defn explain-compiler-report [value]
  (schema/explain compiler-report-schema value options))

(defn explain-order-request [value]
  (schema/explain [:ref :order-request] value options))

(defn explain-decision-model [value]
  (schema/explain [:ref :decision-model] value options))

(defn explain-decision-assurance [value]
  (schema/explain [:ref :decision-assurance] value options))

(defn explain-decision-compiler-artifact [value]
  (schema/explain [:ref :decision-compiler-artifact] value options))

(defn explain-decision-result [value]
  (schema/explain [:ref :decision-result] value options))

(defn explain-decision-report [value]
  (schema/explain [:ref :decision-report] value options))

(defn explain-proof-job-request [value]
  (schema/explain proof-job-request-schema value options))

(defn explain-proof-job-response [value]
  (schema/explain proof-job-response-schema value options))

(defn explain-extension-manifest [value]
  (schema/explain extension-manifest-schema value options))
