(ns rainbow.algorithms.proofs.ahof.cross-validation
  "AHoF V4 worked cross-validation over exact rationals. A two-fold evaluation
  scores the folds 3/4 and 1/4; their total is exactly 1, and dividing by the
  fold count 2 gives the cross-validation mean 1/2. The total and the mean are
  proved by cross-product equivalence, composing the exact list sum with exact
  rational division.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cross-validation`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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
(def score-list (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))
(def one-quarter (make-rational (data-nat 1) (data-nat 3)))
(def half (make-rational (data-nat 1) (data-nat 1)))
(def two (make-rational (data-nat 2) (data-nat 0)))

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
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- nil-scores []
  (function/app (function/const* 'data/nil [type-level]) nnrat))
(defn- cons-score [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))

(def fold-scores (function/const* 'ahof-v4/fold-scores []))
(def fold-count (function/const* 'ahof-v4/fold-count []))

(defn- cross-validation-total [scores]
  (function/app (function/const* 'validation/cross-validation-total []) scores))
(defn- cross-validation-mean [scores count]
  (function/app (function/const* 'validation/cross-validation-mean [])
                scores count))

;; Definitions --------------------------------------------------------------

;; Two folds scored 3/4 and 1/4.
(def fold-scores-spec
  {:name 'ahof-v4/fold-scores :kind :definition :universes []
   :type score-list
   :value (cons-score three-quarters (cons-score one-quarter (nil-scores)))})

(def fold-count-spec
  {:name 'ahof-v4/fold-count :kind :definition :universes []
   :type nnrat :value two})

(def mean-spec
  {:name 'ahof-v4/mean :kind :definition :universes []
   :type nnrat :value (cross-validation-mean fold-scores fold-count)})

(def definition-specs [fold-scores-spec fold-count-spec mean-spec])

;; Theorems -----------------------------------------------------------------

;; The fold total is exactly 1 (3/4 + 1/4).
(def total-is-one-spec
  {:name 'ahof-v4/total-is-one :universes []
   :type (nnrat-equivalent (cross-validation-total fold-scores) nnrat-one)
   :value (equivalent-cross (cross-validation-total fold-scores) nnrat-one)})

;; The cross-validation mean is exactly 1/2 (total 1 over count 2).
(def mean-is-one-half-spec
  {:name 'ahof-v4/mean-is-one-half :universes []
   :type (nnrat-equivalent (function/const* 'ahof-v4/mean []) half)
   :value (equivalent-cross (function/const* 'ahof-v4/mean []) half)})

(def cross-validation-spec
  (let [total-law (:type total-is-one-spec)
        mean-law (:type mean-is-one-half-spec)]
    {:name 'ahof-v4/cross-validation :universes []
     :type (proposition/conjunction total-law mean-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      total-law mean-law
      (function/const* 'ahof-v4/total-is-one [])
      (function/const* 'ahof-v4/mean-is-one-half []))}))

(def theorem-specs
  [total-is-one-spec mean-is-one-half-spec cross-validation-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF cross-validation expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-v4-cross-validation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF cross-validation declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.cross-validation))
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
