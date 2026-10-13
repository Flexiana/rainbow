(ns rainbow.algorithms.proofs.ahof.composite-metric
  "AHoF V5 worked composite metric over exact rationals, combining an accuracy of
  3/4 and a precision of 1/4. With balanced weights 1/2 and 1/2 the composite is
  (1/2)(3/4) + (1/2)(1/4) = 1/2. With accuracy-only weights 1 and 0 the composite
  is (1)(3/4) + (0)(1/4) = 3/4, so the weighting genuinely changes the aggregate.
  The composite values are proved by cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.composite-metric`
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
(def half (make-rational (data-nat 1) (data-nat 1)))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))
(def one-quarter (make-rational (data-nat 1) (data-nat 3)))

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

(defn- composite-metric [weight-a metric-a weight-b metric-b]
  (function/app (function/const* 'validation/composite-metric [])
                weight-a metric-a weight-b metric-b))

(def accuracy (function/const* 'ahof-v5/accuracy []))
(def precision (function/const* 'ahof-v5/precision []))

;; Definitions --------------------------------------------------------------

(def accuracy-spec
  {:name 'ahof-v5/accuracy :kind :definition :universes []
   :type nnrat :value three-quarters})

(def precision-spec
  {:name 'ahof-v5/precision :kind :definition :universes []
   :type nnrat :value one-quarter})

(def balanced-composite-spec
  {:name 'ahof-v5/balanced-composite :kind :definition :universes []
   :type nnrat
   :value (composite-metric half accuracy half precision)})

(def accuracy-weighted-composite-spec
  {:name 'ahof-v5/accuracy-weighted-composite :kind :definition :universes []
   :type nnrat
   :value (composite-metric nnrat-one accuracy nnrat-zero precision)})

(def definition-specs
  [accuracy-spec precision-spec balanced-composite-spec
   accuracy-weighted-composite-spec])

;; Theorems -----------------------------------------------------------------

;; Balanced weights give the average 1/2.
(def balanced-is-one-half-spec
  {:name 'ahof-v5/balanced-is-one-half :universes []
   :type (nnrat-equivalent
          (function/const* 'ahof-v5/balanced-composite []) half)
   :value (equivalent-cross
           (function/const* 'ahof-v5/balanced-composite []) half)})

;; Accuracy-only weights give the accuracy 3/4.
(def accuracy-weighted-is-three-quarters-spec
  {:name 'ahof-v5/accuracy-weighted-is-three-quarters :universes []
   :type (nnrat-equivalent
          (function/const* 'ahof-v5/accuracy-weighted-composite [])
          three-quarters)
   :value (equivalent-cross
           (function/const* 'ahof-v5/accuracy-weighted-composite [])
           three-quarters)})

(def composite-metric-worked-spec
  (let [balanced-law (:type balanced-is-one-half-spec)
        weighted-law (:type accuracy-weighted-is-three-quarters-spec)]
    {:name 'ahof-v5/composite-metric :universes []
     :type (proposition/conjunction balanced-law weighted-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      balanced-law weighted-law
      (function/const* 'ahof-v5/balanced-is-one-half [])
      (function/const* 'ahof-v5/accuracy-weighted-is-three-quarters []))}))

(def theorem-specs
  [balanced-is-one-half-spec accuracy-weighted-is-three-quarters-spec
   composite-metric-worked-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF composite-metric expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-v5-composite-metric}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF composite-metric declaration rejected"
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
