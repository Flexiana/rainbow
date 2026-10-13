(ns rainbow.algorithms.proofs.ahof.knapsack
  "AHoF 0/1 Knapsack (dynamic programming): choose a subset of items maximizing
  total value under a weight capacity. The DP fills a table where each cell is the
  best of two choices -- LEAVE the current item (value of the same capacity with
  fewer items) or TAKE it (its value plus the best value of the remaining
  capacity):

      cell leave-value take-value = max(leave-value, take-value)

  over exact-rational subproblem values, with the DP cell defined as the decidable
  rational max (if leave <= take then take else leave). Proved native and
  axiom-free, as worked instances: cell(5, 7) = 7 (take); cell(8, 3) = 8 (leave);
  and the worked certificates 7 <= 7 and 5 <= 7 (native nnrat/at-most). The DP's
  optimality via optimal substructure is classical and not proved here; the item
  weights/values and the capacity sweep are executable.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.knapsack`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nnrat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- cell [leave-value take-value]
  (function/app (function/const* 'knapsack/cell []) leave-value take-value))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell leave take = if leave <= take then take else leave  (best of the two)
(def cell-spec
  {:name 'knapsack/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['leave-value nnrat] ['take-value nnrat]]
                        (if-nnrat (decide-at-most 'leave-value 'take-value)
                                  'take-value 'leave-value))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

;; Taking the item (value 7) beats leaving it (value 5): the cell is 7.
(def takes-when-better-spec
  {:name 'knapsack/takes-when-better :universes []
   :type (equality nnrat (cell (whole 5) (whole 7)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 5) (whole 7)))})

;; Leaving the item (value 8) beats taking it (value 3): the cell is 8.
(def leaves-when-better-spec
  {:name 'knapsack/leaves-when-better :universes []
   :type (equality nnrat (cell (whole 8) (whole 3)) (whole 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 8) (whole 3)))})

;; Worked certificate: the take value 7 is at most the cell value 7.
(def dominates-take-spec
  {:name 'knapsack/dominates-take :universes []
   :type (nnrat-at-most (whole 7) (whole 7))
   :value (at-most-proof (whole 7) (whole 7))})

;; Worked certificate: the leave value 5 is at most the cell value 7.
(def dominates-leave-spec
  {:name 'knapsack/dominates-leave :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

(def theorem-specs
  [takes-when-better-spec leaves-when-better-spec dominates-take-spec
   dominates-leave-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-knapsack
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
