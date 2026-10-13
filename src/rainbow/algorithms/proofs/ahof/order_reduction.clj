(ns rainbow.algorithms.proofs.ahof.order-reduction
  "AHoF V38 Order Reduction: reduce the generator/complexity order of a set
  representation while over-approximating; the reduction is sound when the incurred
  over-approximation error stays within the tolerance:

      reduction-sound? error tolerance = decide (error <= tolerance).
  Proved native and axiom-free (decision, two positive instances, at-most certificate,
  negative instance). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.order-reduction`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- pred [a b] (function/app (function/const* 'order-reduction/reduction-sound? []) a b))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def pred-spec
  {:name 'order-reduction/reduction-sound? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['error nnrat] ['tolerance nnrat]] (decide-at-most 'error 'tolerance))})

(def definition-specs [pred-spec])

(def small-error-sound-spec
  {:name 'order-reduction/small-error-sound :universes []
   :type (equality bool (pred (fraction 1 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 3) (fraction 1 1)))})

(def boundary-sound-spec
  {:name 'order-reduction/boundary-sound :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 1 1)))})

(def error-certificate-spec
  {:name 'order-reduction/error-certificate :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def large-error-unsound-spec
  {:name 'order-reduction/large-error-unsound :universes []
   :type (equality bool (pred (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [small-error-sound-spec boundary-sound-spec error-certificate-spec large-error-unsound-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-order-reduction
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
