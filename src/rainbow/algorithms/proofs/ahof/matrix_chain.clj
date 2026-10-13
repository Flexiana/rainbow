(ns rainbow.algorithms.proofs.ahof.matrix-chain
  "AHoF Matrix Chain Multiplication (dynamic programming): find the
  parenthesization of a chain of matrix products that minimizes the number of
  scalar multiplications. The DP considers every split point k: the cost is the
  cost of the left sub-chain plus the cost of the right sub-chain plus the cost of
  multiplying the two resulting matrices,

      split-cost left right multiply = left + right + multiply

  and each cell takes the minimum split cost (better-split, a decidable rational
  min). Proved native and axiom-free, as worked instances: split-cost(2, 3, 4) = 9;
  better-split(9, 6) = 6; and the worked certificate 6 <= 9 (native
  nnrat/at-most). The DP's optimal parenthesization is classical and not proved
  here; the dimension array and the split sweep are executable.

  Requires nnrat/add, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.matrix-chain`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
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

(defn- split-cost [left right multiply]
  (function/app (function/const* 'matrix-chain/split-cost []) left right multiply))
(defn- better-split [current-best candidate]
  (function/app (function/const* 'matrix-chain/better-split []) current-best candidate))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; split-cost left right multiply = left + right + multiply
(def split-cost-spec
  {:name 'matrix-chain/split-cost :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['left nnrat] ['right nnrat] ['multiply nnrat]]
                        (nnrat-add (nnrat-add 'left 'right) 'multiply))})

;; better-split current-best candidate = if candidate <= current-best
;;                                       then candidate else current-best (min)
(def better-split-spec
  {:name 'matrix-chain/better-split :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current-best nnrat] ['candidate nnrat]]
                        (if-nnrat (decide-at-most 'candidate 'current-best)
                                  'candidate 'current-best))})

(def definition-specs [split-cost-spec better-split-spec])

;; Theorems -----------------------------------------------------------------

;; A split with sub-costs 2 and 3 and multiply cost 4 costs 9.
(def split-cost-example-spec
  {:name 'matrix-chain/split-cost-example :universes []
   :type (equality nnrat (split-cost (whole 2) (whole 3) (whole 4)) (whole 9))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (split-cost (whole 2) (whole 3) (whole 4)))})

;; The cheaper split (cost 6) beats the current best (9): the cell is 6.
(def takes-cheaper-split-spec
  {:name 'matrix-chain/takes-cheaper-split :universes []
   :type (equality nnrat (better-split (whole 9) (whole 6)) (whole 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (better-split (whole 9) (whole 6)))})

;; Worked certificate for the cell above: 6 <= 9.
(def chosen-split-is-minimal-spec
  {:name 'matrix-chain/chosen-split-is-minimal :universes []
   :type (nnrat-at-most (whole 6) (whole 9))
   :value (at-most-proof (whole 6) (whole 9))})

(def theorem-specs
  [split-cost-example-spec takes-cheaper-split-spec chosen-split-is-minimal-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-matrix-chain (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.matrix-chain))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
