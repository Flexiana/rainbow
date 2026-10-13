(ns rainbow.algorithms.proofs.ahof.coin-change
  "AHoF Coin Change (dynamic programming): the minimum number of coins that sum to
  a target amount, from unlimited coins of given denominations -- the canonical
  unbounded-knapsack-style min-DP. Each cell for amount a is the minimum over
  denominations c of 1 + dp(a - c); comparing the running best against a new
  candidate is:

      cell current-best candidate = if candidate <= current-best
                                    then candidate else current-best

  (keep the smaller coin count), over exact-rational counts. Proved native and
  axiom-free: the DP cell as the decidable rational min (via logic/if-data); a
  worked cell taking the cheaper candidate; a worked cell keeping the current
  best; and the certificates that the cell value is at most BOTH the candidate and
  the current best (native nnrat/at-most) -- it is their minimum. The
  denomination sweep and unreachable-amount handling are executable; what is
  proved is the min-DP cell choice.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.coin-change`
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

(defn- cell [current-best candidate]
  (function/app (function/const* 'coin-change/cell []) current-best candidate))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell current-best candidate = if candidate <= current-best then candidate
;;                               else current-best   (the minimum)
(def cell-spec
  {:name 'coin-change/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current-best nnrat] ['candidate nnrat]]
                        (if-nnrat (decide-at-most 'candidate 'current-best)
                                  'candidate 'current-best))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

;; A cheaper candidate (3 coins) beats the current best (5): the cell is 3.
(def takes-cheaper-candidate-spec
  {:name 'coin-change/takes-cheaper-candidate :universes []
   :type (equality nnrat (cell (whole 5) (whole 3)) (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 5) (whole 3)))})

;; A worse candidate (7 coins) leaves the current best (4) unchanged.
(def keeps-current-best-spec
  {:name 'coin-change/keeps-current-best :universes []
   :type (equality nnrat (cell (whole 4) (whole 7)) (whole 4))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 4) (whole 7)))})

;; Certificate: the cell value is at most the candidate (3 <= 3) ...
(def at-most-candidate-spec
  {:name 'coin-change/at-most-candidate :universes []
   :type (nnrat-at-most (whole 3) (whole 3))
   :value (at-most-proof (whole 3) (whole 3))})

;; ... and at most the previous best (3 <= 5): the cell is their minimum.
(def at-most-current-spec
  {:name 'coin-change/at-most-current :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

(def theorem-specs
  [takes-cheaper-candidate-spec keeps-current-best-spec at-most-candidate-spec
   at-most-current-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-coin-change
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
