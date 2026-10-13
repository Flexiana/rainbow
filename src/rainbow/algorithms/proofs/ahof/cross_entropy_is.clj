(ns rainbow.algorithms.proofs.ahof.cross-entropy-is
  "AHoF V29 Cross-Entropy Importance Sampling: iteratively fit the sampling
  distribution to the rare failure region by keeping the elite samples -- those whose
  cost falls at or below the current elite quantile threshold:

      elite? cost threshold = decide (cost <= threshold).
  Proved native and axiom-free (decision, two positive instances, at-most certificate,
  negative instance). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cross-entropy-is`
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
(defn- pred [a b] (function/app (function/const* 'ce-is/elite? []) a b))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def pred-spec
  {:name 'ce-is/elite? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cost nnrat] ['threshold nnrat]] (decide-at-most 'cost 'threshold))})

(def definition-specs [pred-spec])

(def low-cost-is-elite-spec
  {:name 'ce-is/low-cost-is-elite :universes []
   :type (equality bool (pred (fraction 1 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 3) (fraction 1 1)))})

(def boundary-is-elite-spec
  {:name 'ce-is/boundary-is-elite :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 1 1)))})

(def elite-certificate-spec
  {:name 'ce-is/elite-certificate :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def high-cost-not-elite-spec
  {:name 'ce-is/high-cost-not-elite :universes []
   :type (equality bool (pred (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [low-cost-is-elite-spec boundary-is-elite-spec elite-certificate-spec high-cost-not-elite-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-cross-entropy-is
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
