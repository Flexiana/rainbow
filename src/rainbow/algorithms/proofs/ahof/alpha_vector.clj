(ns rainbow.algorithms.proofs.ahof.alpha-vector
  "AHoF D71 Alpha Vector (Exact POMDP value function): the optimal value at a belief b
  is the maximum over the alpha-vector set of the inner products <alpha, b>. With two
  alpha vectors the value picks the larger of the two dot products, and the dominant
  vector is the one whose value is at least the other's:

      selects-dominant? v0 v1 = decide (v1 <= v0)
      best-value        v0 v1 = if (v1 <= v0) then v0 else v1   (the larger value)

  over exact rationals. Proved native and axiom-free: the dominance decision, the
  best-value (max) selection, and the switch when the second vector dominates.
  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.alpha-vector`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- selects-dominant? [v0 v1]
  (function/app (function/const* 'alpha-vector/selects-dominant? []) v0 v1))
(defn- best-value [v0 v1]
  (function/app (function/const* 'alpha-vector/best-value []) v0 v1))

(def selects-spec
  {:name 'alpha-vector/selects-dominant? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['v0 nnrat] ['v1 nnrat]] (decide-at-most 'v1 'v0))})

(def best-value-spec
  {:name 'alpha-vector/best-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['v0 nnrat] ['v1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'v1 'v0))
                                      (decide-at-most 'v1 'v0) 'v0 'v1))})

(def definition-specs [selects-spec best-value-spec])

(def dominant-vector-selected-spec
  {:name 'alpha-vector/dominant-vector-selected :universes []
   :type (equality bool (selects-dominant? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (selects-dominant? (fraction 3 3) (fraction 1 1)))})

(def value-is-maximum-spec
  {:name 'alpha-vector/value-is-maximum :universes []
   :type (equality nnrat (best-value (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-value (fraction 3 3) (fraction 1 1)))})

(def switches-dominance-spec
  {:name 'alpha-vector/switches-dominance :universes []
   :type (equality bool (selects-dominant? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (selects-dominant? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [dominant-vector-selected-spec value-is-maximum-spec switches-dominance-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-alpha-vector (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.alpha-vector))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
