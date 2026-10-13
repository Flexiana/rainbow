(ns rainbow.algorithms.proofs.ahof.importance-sampling
  "AHoF D7 worked likelihood-weighted (importance) sampling over exact rationals.
  Two samples carry unnormalized likelihood weights 3 and 1 and values 1 and 0.
  The weighted sum is 3 * 1 + 1 * 0 = 3 and the total weight is 3 + 1 = 4, so the
  importance estimate is 3 / 4 -- the normalization by the total weight matters
  because the weights do not sum to one. The values are proved by cross-product
  equivalence.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.importance-sampling`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def three (make-rational (data-nat 3) (data-nat 0)))
(def four (make-rational (data-nat 4) (data-nat 0)))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

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

;; Samples: weight 3 with value 1, weight 1 with value 0.
(def sample-weighted-sum-spec
  {:name 'ahof-d7/sample-weighted-sum :kind :definition :universes []
   :type nnrat
   :value (weighted-sum three nnrat-one nnrat-one nnrat-zero)})

(def sample-total-weight-spec
  {:name 'ahof-d7/sample-total-weight :kind :definition :universes []
   :type nnrat :value (total-weight three nnrat-one)})

(def sample-estimate-spec
  {:name 'ahof-d7/sample-estimate :kind :definition :universes []
   :type nnrat
   :value (importance-estimate three nnrat-one nnrat-one nnrat-zero)})

(def definition-specs
  [sample-weighted-sum-spec sample-total-weight-spec sample-estimate-spec])

;; Theorems -----------------------------------------------------------------

(def weighted-sum-is-three-spec
  {:name 'ahof-d7/weighted-sum-is-three :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d7/sample-weighted-sum [])
                           three)
   :value (equivalent-cross (function/const* 'ahof-d7/sample-weighted-sum [])
                            three)})

(def total-weight-is-four-spec
  {:name 'ahof-d7/total-weight-is-four :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d7/sample-total-weight [])
                           four)
   :value (equivalent-cross (function/const* 'ahof-d7/sample-total-weight [])
                            four)})

(def estimate-is-three-quarters-spec
  {:name 'ahof-d7/estimate-is-three-quarters :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d7/sample-estimate [])
                           three-quarters)
   :value (equivalent-cross (function/const* 'ahof-d7/sample-estimate [])
                            three-quarters)})

(def importance-sampling-spec
  (let [sum-law (:type weighted-sum-is-three-spec)
        weight-law (:type total-weight-is-four-spec)
        estimate-law (:type estimate-is-three-quarters-spec)]
    {:name 'ahof-d7/importance-sampling :universes []
     :type (proposition/conjunction
            sum-law (proposition/conjunction weight-law estimate-law))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      sum-law (proposition/conjunction weight-law estimate-law)
      (function/const* 'ahof-d7/weighted-sum-is-three [])
      (function/app
       (function/const* 'proposition/conjoin [])
       weight-law estimate-law
       (function/const* 'ahof-d7/total-weight-is-four [])
       (function/const* 'ahof-d7/estimate-is-three-quarters [])))}))

(def theorem-specs
  [weighted-sum-is-three-spec total-weight-is-four-spec
   estimate-is-three-quarters-spec importance-sampling-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF importance-sampling expression failed elaboration"
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
          :rainbow/provenance
          {:origin :native :producer :ahof-d7-importance-sampling}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF importance-sampling declaration rejected"
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
