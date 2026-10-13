(ns rainbow.math.or-foundation
  "Small reusable proof-data laws shared by OR representations."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])

(defn product [left right]
  (function/app (function/const* 'data/Product [data-level data-level])
                left right))

(defn pair [left right first-value second-value]
  (function/app (function/const* 'data/pair [data-level data-level])
                left right first-value second-value))

(defn first-projection [left right value]
  (function/app (function/const* 'product/first [data-level data-level])
                left right value))

(def product-diagonal-injective-spec
  (let [product-a (product 'A 'A)
        diagonal (function/lam [['value 'A]] (pair 'A 'A 'value 'value))
        first-map (function/lam [['value product-a]]
                               (first-projection 'A 'A 'value))]
    {:name 'function/product-diagonal-injective
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (function/injective data-level data-level 'A product-a diagonal))
     :value
     (function/lam
      [['A type-u :implicit] ['left 'A] ['right 'A]
       ['same-pair
        (function/equality
         data-level product-a
         (pair 'A 'A 'left 'left)
         (pair 'A 'A 'right 'right))]]
      (function/app
       (function/const* 'equality/congruent-function
                        [data-level data-level])
       product-a 'A first-map
       (pair 'A 'A 'left 'left)
       (pair 'A 'A 'right 'right)
       'same-pair))}))

(def theorem-specs [product-diagonal-injective-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "OR foundation theorem failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-theorem [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :operations-research-foundation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "OR foundation theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-theorem checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
