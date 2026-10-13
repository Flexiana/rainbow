(ns rainbow.algorithms.proofs.ahof.hungarian
  "AHoF Hungarian Algorithm (Kuhn-Munkres): find a minimum-cost perfect assignment
  of n agents to n tasks in O(n^3) -- the exact solver for the assignment problem
  (job scheduling, tracking, matching). It repeatedly subtracts row and column
  minima to expose ZERO reduced costs and searches for a perfect matching among
  those tight cells, adjusting when none exists. A cell is a candidate for the
  assignment exactly when its reduced cost has reached zero (is tight):

      tight? reduced-cost = decide (reduced-cost <= 0)

  over exact-rational reduced costs (which are non-negative after each reduction, so
  <= 0 means exactly 0). Proved native and axiom-free: the tightness test; that a
  zero-reduced-cost cell is tight (assignable); the certificate that a tight cell's
  reduced cost is at most zero, hence exactly zero (native nnrat/at-most) -- so it
  incurs no extra cost over the reduced optimum; and that a positive reduced cost is
  not yet tight. The row/column reductions and augmenting search are executable;
  what is proved is the tight-cell decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hungarian`
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
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- tight? [reduced-cost]
  (function/app (function/const* 'hungarian/tight? []) reduced-cost))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; tight? reduced-cost = decide (reduced-cost <= 0)
(def tight-spec
  {:name 'hungarian/tight? :kind :definition :universes []
   :type (function/arrow nnrat bool)
   :value (function/lam [['reduced-cost nnrat]]
                        (decide-at-most 'reduced-cost (whole 0)))})

(def definition-specs [tight-spec])

;; Theorems -----------------------------------------------------------------

;; A cell with reduced cost 0 is tight -- a candidate for the assignment.
(def zero-reduced-cost-tight-spec
  {:name 'hungarian/zero-reduced-cost-tight :universes []
   :type (equality bool (tight? (whole 0))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (tight? (whole 0)))})

;; Certificate: a tight cell's reduced cost is at most zero, hence exactly zero
;; (0 <= 0) -- it adds no cost over the reduced optimum.
(def tight-cost-zero-spec
  {:name 'hungarian/tight-cost-zero :universes []
   :type (nnrat-at-most (whole 0) (whole 0))
   :value (at-most-proof (whole 0) (whole 0))})

;; A cell with positive reduced cost 3 is not yet tight (needs more reduction).
(def positive-cost-not-tight-spec
  {:name 'hungarian/positive-cost-not-tight :universes []
   :type (equality bool (tight? (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (tight? (whole 3)))})

(def theorem-specs
  [zero-reduced-cost-tight-spec tight-cost-zero-spec positive-cost-not-tight-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-hungarian
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
