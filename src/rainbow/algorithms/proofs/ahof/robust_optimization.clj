(ns rainbow.algorithms.proofs.ahof.robust-optimization
  "AHoF O74 Robust Optimization (set-based): optimize against the WORST case over an
  uncertainty set. With two scenario costs the worst case is their maximum, and a
  design is robustly acceptable when that worst case stays within the budget:

      worst-case  c1 c2        = if (c1 <= c2) then c2 else c1   (maximum)
      robust-ok?  worst budget = decide (worst <= budget)

  over exact rationals. Proved native and axiom-free: the worst-case (max) selection
  in both orders, and the robust-acceptance threshold decision. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.robust-optimization`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))

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
(defn- whole [n] (fraction n 0))

(defn- worst-case [c1 c2]
  (function/app (function/const* 'robust-opt/worst-case []) c1 c2))
(defn- robust-ok? [worst budget]
  (function/app (function/const* 'robust-opt/robust-ok? []) worst budget))

;; worst-case c1 c2 = if (c1 <= c2) then c2 else c1   (maximum)
(def worst-case-spec
  {:name 'robust-opt/worst-case :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['c1 nnrat] ['c2 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'c1 'c2))
                                      (decide-at-most 'c1 'c2) 'c2 'c1))})

;; robust-ok? worst budget = decide (worst <= budget)
(def robust-ok-spec
  {:name 'robust-opt/robust-ok? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['worst nnrat] ['budget nnrat]]
                        (decide-at-most 'worst 'budget))})

(def definition-specs [worst-case-spec robust-ok-spec])

;; The worst case of 1/2 and 3/4 is 3/4.
(def worst-case-is-larger-spec
  {:name 'robust-opt/worst-case-is-larger :universes []
   :type (equality nnrat (worst-case (fraction 1 1) (fraction 3 3)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (worst-case (fraction 1 1) (fraction 3 3)))})

;; ...and the same with the scenarios swapped.
(def worst-case-symmetric-spec
  {:name 'robust-opt/worst-case-symmetric :universes []
   :type (equality nnrat (worst-case (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (worst-case (fraction 3 3) (fraction 1 1)))})

;; A worst case of 3/4 is within a budget of 1: the design is robustly acceptable.
(def within-budget-spec
  {:name 'robust-opt/within-budget :universes []
   :type (equality bool (robust-ok? (fraction 3 3) (whole 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (robust-ok? (fraction 3 3) (whole 1)))})

(def theorem-specs
  [worst-case-is-larger-spec worst-case-symmetric-spec within-budget-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-robust-optimization
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
