(ns rainbow.algorithms.proofs.importance-sampling
  "Likelihood-weighted (importance) sampling estimates over exact rationals. Each
  sample carries a likelihood weight and a value; the importance estimate is the
  weight-weighted sum of the values divided by the total weight -- normalizing by
  the total weight so that unnormalized likelihood weights still yield a proper
  estimate (AHoF D7). This composes exact-rational multiplication and addition
  (the weighted sum and total weight) with exact rational division (the
  normalization).

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.importance-sampling`
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
(defn- nnrat-divide [total count]
  (function/app (function/const* 'nnrat/divide []) total count))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- weighted-sum [weight-a value-a weight-b value-b]
  (function/app (function/const* 'estimation/weighted-sum [])
                weight-a value-a weight-b value-b))
(defn- total-weight [weight-a weight-b]
  (function/app (function/const* 'estimation/total-weight [])
                weight-a weight-b))
(defn- importance-estimate [weight-a value-a weight-b value-b]
  (function/app (function/const* 'estimation/importance-estimate [])
                weight-a value-a weight-b value-b))

;; Definitions --------------------------------------------------------------

;; The weight-weighted sum of the sample values.
(def weighted-sum-spec
  {:name 'estimation/weighted-sum :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['weight-a nnrat] ['value-a nnrat]
                         ['weight-b nnrat] ['value-b nnrat]]
                        (nnrat-add (nnrat-multiply 'weight-a 'value-a)
                                   (nnrat-multiply 'weight-b 'value-b)))})

;; The total sample weight.
(def total-weight-spec
  {:name 'estimation/total-weight :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['weight-a nnrat] ['weight-b nnrat]]
                        (nnrat-add 'weight-a 'weight-b))})

;; The importance estimate: weighted sum normalized by the total weight.
(def importance-estimate-spec
  {:name 'estimation/importance-estimate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['weight-a nnrat] ['value-a nnrat]
                         ['weight-b nnrat] ['value-b nnrat]]
                        (nnrat-divide
                         (weighted-sum 'weight-a 'value-a 'weight-b 'value-b)
                         (total-weight 'weight-a 'weight-b)))})

(def definition-specs
  [weighted-sum-spec total-weight-spec importance-estimate-spec])

;; Theorems -----------------------------------------------------------------

(def weighted-sum-unfold-spec
  {:name 'estimation/weighted-sum-unfold :universes []
   :type (function/forall
          [['weight-a nnrat] ['value-a nnrat] ['weight-b nnrat]
           ['value-b nnrat]]
          (equality nnrat
                    (weighted-sum 'weight-a 'value-a 'weight-b 'value-b)
                    (nnrat-add (nnrat-multiply 'weight-a 'value-a)
                               (nnrat-multiply 'weight-b 'value-b))))
   :value (function/lam [['weight-a nnrat] ['value-a nnrat] ['weight-b nnrat]
                         ['value-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (weighted-sum 'weight-a 'value-a 'weight-b
                                             'value-b)))})

(def importance-estimate-unfold-spec
  {:name 'estimation/importance-estimate-unfold :universes []
   :type (function/forall
          [['weight-a nnrat] ['value-a nnrat] ['weight-b nnrat]
           ['value-b nnrat]]
          (equality nnrat
                    (importance-estimate 'weight-a 'value-a 'weight-b 'value-b)
                    (nnrat-divide
                     (weighted-sum 'weight-a 'value-a 'weight-b 'value-b)
                     (total-weight 'weight-a 'weight-b))))
   :value (function/lam [['weight-a nnrat] ['value-a nnrat] ['weight-b nnrat]
                         ['value-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (importance-estimate 'weight-a 'value-a 'weight-b
                                                    'value-b)))})

(def theorem-specs
  [weighted-sum-unfold-spec importance-estimate-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Importance-sampling expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :importance-sampling}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Importance-sampling declaration rejected"
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
