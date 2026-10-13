(ns rainbow.algorithms.proofs.ahof.confidence-interval
  "AHoF Confidence Interval: quantify the uncertainty of a point estimate by an
  interval that, over repeated sampling, covers the true parameter with a chosen
  confidence level (e.g. 95%). A symmetric interval is estimate +/- margin, where
  margin = z * standard-error; the interval [lower, upper] CONTAINS a value exactly
  when the value lies at or above the lower bound and at or below the upper bound:

      contains? value lower upper = (lower <= value) AND (value <= upper)

  over exact-rational bounds. Proved native and axiom-free: the containment test as
  a boolean conjunction of two decidable comparisons (via logic/if-data over Bool);
  that a value inside the interval is contained; that a value above the upper bound
  is not; and the certificates that a contained value satisfies both bounds
  (native nnrat/at-most). The estimate, standard error, and critical value are
  executable; what is proved is the interval-containment decision -- the coverage
  check behind confidence intervals.

  Requires nnrat/at-most, audit/decide-nnrat-at-most, logic/if-data,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.confidence-interval`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- contains? [value lower upper]
  (function/app (function/const* 'confidence-interval/contains? []) value lower upper))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; contains? value lower upper = (lower <= value) AND (value <= upper)
(def contains-spec
  {:name 'confidence-interval/contains? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam
           [['value nnrat] ['lower nnrat] ['upper nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'lower 'value))
                         (decide-at-most 'lower 'value)
                         (decide-at-most 'value 'upper)
                         false-value))})

(def definition-specs [contains-spec])

;; Theorems -----------------------------------------------------------------

;; A value 5 inside the interval [3, 7] is contained.
(def contains-interior-value-spec
  {:name 'confidence-interval/contains-interior-value :universes []
   :type (equality bool (contains? (whole 5) (whole 3) (whole 7))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (contains? (whole 5) (whole 3) (whole 7)))})

;; A value 8 above the upper bound of [3, 7] is not contained.
(def excludes-value-above-spec
  {:name 'confidence-interval/excludes-value-above :universes []
   :type (equality bool (contains? (whole 8) (whole 3) (whole 7))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (contains? (whole 8) (whole 3) (whole 7)))})

;; Certificate: a contained value is at least the lower bound (3 <= 5) ...
(def contained-meets-lower-spec
  {:name 'confidence-interval/contained-meets-lower :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; ... and at most the upper bound (5 <= 7).
(def contained-meets-upper-spec
  {:name 'confidence-interval/contained-meets-upper :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

(def theorem-specs
  [contains-interior-value-spec excludes-value-above-spec
   contained-meets-lower-spec contained-meets-upper-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-confidence-interval
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
