(ns rainbow.algorithms.proofs.ahof.weighted-interval
  "AHoF Weighted Interval Scheduling (dynamic programming): given intervals with
  weights (values), select a mutually-compatible subset of MAXIMUM total weight.
  Unlike unweighted activity selection (which is greedy), the weighted version
  needs DP: sort by finish time, and for each interval j decide whether INCLUDING
  it (its weight plus the best solution among intervals compatible with it) beats
  EXCLUDING it (the best solution over the earlier intervals):

      cell include-value exclude-value = max(include-value, exclude-value)

  over exact-rational values. Proved native and axiom-free: the DP cell as the
  decidable rational max (via logic/if-data); a worked cell that includes the
  interval; a worked cell that excludes it; and the certificates that the chosen
  value dominates BOTH the include and exclude options (native nnrat/at-most). The
  predecessor computation (latest compatible interval) and the finish-time sort
  are executable; what is proved is the include/exclude max choice.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.weighted-interval`
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

(defn- cell [include-value exclude-value]
  (function/app (function/const* 'weighted-interval/cell []) include-value exclude-value))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell include exclude = max(include, exclude)
(def cell-spec
  {:name 'weighted-interval/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['include-value nnrat] ['exclude-value nnrat]]
                        (if-nnrat (decide-at-most 'include-value 'exclude-value)
                                  'exclude-value 'include-value))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

;; Including the interval (value 7) beats excluding it (value 5): the cell is 7.
(def includes-when-better-spec
  {:name 'weighted-interval/includes-when-better :universes []
   :type (equality nnrat (cell (whole 7) (whole 5)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 7) (whole 5)))})

;; Excluding the interval (value 8) beats including it (value 4): the cell is 8.
(def excludes-when-better-spec
  {:name 'weighted-interval/excludes-when-better :universes []
   :type (equality nnrat (cell (whole 4) (whole 8)) (whole 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 4) (whole 8)))})

;; The cell value dominates the include option (7 <= 7).
(def dominates-include-spec
  {:name 'weighted-interval/dominates-include :universes []
   :type (nnrat-at-most (whole 7) (whole 7))
   :value (at-most-proof (whole 7) (whole 7))})

;; The cell value dominates the exclude option (5 <= 7).
(def dominates-exclude-spec
  {:name 'weighted-interval/dominates-exclude :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

(def theorem-specs
  [includes-when-better-spec excludes-when-better-spec dominates-include-spec
   dominates-exclude-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-weighted-interval (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.weighted-interval))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
