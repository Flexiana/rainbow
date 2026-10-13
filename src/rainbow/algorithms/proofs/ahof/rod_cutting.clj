(ns rainbow.algorithms.proofs.ahof.rod-cutting
  "AHoF Rod Cutting (dynamic programming): given a rod of integer length and a
  price for each possible piece length, cut it into pieces maximizing total
  revenue. The DP for length n takes the maximum over first-cut lengths i of
  price(i) + best-revenue(n - i); comparing the running best against a new cut's
  revenue is:

      cell current-best cut-revenue = max(current-best, cut-revenue)

  where cut-revenue = price(i) + revenue(n - i), over exact-rational revenues.
  Proved native and axiom-free: the DP cell as the decidable rational max (if
  current-best <= cut-revenue then cut-revenue else current-best); a worked cell
  taking a more profitable cut; a worked cell keeping the current best; and the
  certificates that the chosen revenue dominates BOTH options (native
  nnrat/at-most). The price table and the length sweep are executable; what is
  proved is the revenue-maximizing cut choice.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rod-cutting`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- cell [current-best cut-revenue]
  (function/app (function/const* 'rod-cutting/cell []) current-best cut-revenue))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell current-best cut-revenue = max(current-best, cut-revenue)
(def cell-spec
  {:name 'rod-cutting/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current-best nnrat] ['cut-revenue nnrat]]
                        (if-nnrat (decide-at-most 'current-best 'cut-revenue)
                                  'cut-revenue 'current-best))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

;; A more profitable cut (revenue 8) beats the current best (5): the cell is 8.
(def takes-better-cut-spec
  {:name 'rod-cutting/takes-better-cut :universes []
   :type (equality nnrat (cell (whole 5) (whole 8)) (whole 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 5) (whole 8)))})

;; A worse cut (revenue 3) leaves the current best (7) unchanged.
(def keeps-best-cut-spec
  {:name 'rod-cutting/keeps-best-cut :universes []
   :type (equality nnrat (cell (whole 7) (whole 3)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 7) (whole 3)))})

;; The cell value dominates the cut revenue (8 <= 8) ...
(def dominates-cut-spec
  {:name 'rod-cutting/dominates-cut :universes []
   :type (nnrat-at-most (whole 8) (whole 8))
   :value (at-most-proof (whole 8) (whole 8))})

;; ... and the previous best (5 <= 8): the cell is their maximum.
(def dominates-previous-spec
  {:name 'rod-cutting/dominates-previous :universes []
   :type (nnrat-at-most (whole 5) (whole 8))
   :value (at-most-proof (whole 5) (whole 8))})

(def theorem-specs
  [takes-better-cut-spec keeps-best-cut-spec dominates-cut-spec
   dominates-previous-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-rod-cutting (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.rod-cutting))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
