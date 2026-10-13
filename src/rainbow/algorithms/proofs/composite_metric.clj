(ns rainbow.algorithms.proofs.composite-metric
  "Composite evaluation metrics over exact rationals. A composite metric is a
  weighted combination of atomic metrics: given weights and atomic metric values,
  the composite is `w1 * m1 + w2 * m2`. This composes exact-rational multiplication
  and addition to aggregate several atomic metrics into one score (AHoF V5). When
  the weights sum to one the composite is a weighted average of the metrics.

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.composite-metric`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- composite-metric [weight-a metric-a weight-b metric-b]
  (function/app (function/const* 'validation/composite-metric [])
                weight-a metric-a weight-b metric-b))

;; Definitions --------------------------------------------------------------

;; A composite metric weights two atomic metrics and sums them.
(def composite-metric-spec
  {:name 'validation/composite-metric :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['weight-a nnrat] ['metric-a nnrat]
                         ['weight-b nnrat] ['metric-b nnrat]]
                        (nnrat-add
                         (nnrat-multiply 'weight-a 'metric-a)
                         (nnrat-multiply 'weight-b 'metric-b)))})

(def definition-specs [composite-metric-spec])

;; Theorems -----------------------------------------------------------------

(def composite-metric-unfold-spec
  {:name 'validation/composite-metric-unfold :universes []
   :type (function/forall
          [['weight-a nnrat] ['metric-a nnrat] ['weight-b nnrat]
           ['metric-b nnrat]]
          (equality nnrat
                    (composite-metric 'weight-a 'metric-a 'weight-b 'metric-b)
                    (nnrat-add (nnrat-multiply 'weight-a 'metric-a)
                               (nnrat-multiply 'weight-b 'metric-b))))
   :value (function/lam [['weight-a nnrat] ['metric-a nnrat] ['weight-b nnrat]
                         ['metric-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (composite-metric 'weight-a 'metric-a 'weight-b
                                                 'metric-b)))})

(def theorem-specs [composite-metric-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Composite-metric expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :composite-metric}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Composite-metric declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
