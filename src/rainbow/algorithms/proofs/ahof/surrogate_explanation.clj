(ns rainbow.algorithms.proofs.ahof.surrogate-explanation
  "AHoF V56 Surrogate Model Explanation: fit an interpretable surrogate to a black-box
  model and explain via the surrogate; the explanation is faithful when the surrogate's
  local fidelity error is within the tolerance:

      faithful? error tolerance = decide (error <= tolerance).
  Proved native and axiom-free (decision, two positive instances, at-most certificate,
  negative instance). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.surrogate-explanation`
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
(defn- pred [a b] (function/app (function/const* 'surrogate-exp/faithful? []) a b))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def pred-spec
  {:name 'surrogate-exp/faithful? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['error nnrat] ['tolerance nnrat]] (decide-at-most 'error 'tolerance))})

(def definition-specs [pred-spec])

(def low-error-faithful-spec
  {:name 'surrogate-exp/low-error-faithful :universes []
   :type (equality bool (pred (fraction 1 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 3) (fraction 1 1)))})

(def boundary-faithful-spec
  {:name 'surrogate-exp/boundary-faithful :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 1 1)))})

(def fidelity-certificate-spec
  {:name 'surrogate-exp/fidelity-certificate :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def high-error-unfaithful-spec
  {:name 'surrogate-exp/high-error-unfaithful :universes []
   :type (equality bool (pred (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [low-error-faithful-spec boundary-faithful-spec fidelity-certificate-spec high-error-unfaithful-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-surrogate-explanation
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
