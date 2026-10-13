(ns rainbow.algorithms.proofs.ahof.column-generation
  "AHoF O-family Column Generation: solve a large linear program with too many
  variables to enumerate by working with a small RESTRICTED master problem and
  generating new columns only as needed. The pricing subproblem asks whether any
  not-yet-included column would improve the objective. Classically a column can
  improve a minimization objective when its reduced cost (cost - dual, with dual
  the price of the constraints it serves) is strictly negative, i.e. cost < dual.
  The test here is non-strict:

      worth-adding? cost dual = decide (cost <= dual)

  over exact rationals, so it accepts every column of NONPOSITIVE reduced cost,
  including cost = dual (reduced cost zero, e.g. cost 5 with dual 5), which does
  not strictly improve the objective. Defined: the pricing test. Proved native
  and axiom-free, as worked instances: a column of cost 3 with dual value 5
  prices favorably, a column of cost 7 with dual value 5 does not, and the worked
  certificate 3 <= 5 (native nnrat/at-most). The classical guarantees (an added
  column improves or maintains the objective; when no column has strictly
  negative reduced cost the current basis is optimal) are not proved here. The
  subproblem solver and the master LP are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.column-generation`
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

(defn- worth-adding? [cost dual]
  (function/app (function/const* 'column-generation/worth-adding? []) cost dual))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; worth-adding? cost dual = decide (cost <= dual)  (nonpositive reduced cost)
(def worth-adding-spec
  {:name 'column-generation/worth-adding? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cost nnrat] ['dual nnrat]]
                        (decide-at-most 'cost 'dual))})

(def definition-specs [worth-adding-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A column costing 3 whose dual value is 5 prices favorably -> add it.
(def prices-favorably-spec
  {:name 'column-generation/prices-favorably :universes []
   :type (equality bool (worth-adding? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (worth-adding? (whole 3) (whole 5)))})

;; Worked certificate 3 <= 5. That adding such a column improves (or maintains)
;; the objective is classical and not proved here.
(def added-column-improves-spec
  {:name 'column-generation/added-column-improves :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A column costing 7 whose dual value is only 5 does not price favorably. The
;; classical optimality of the basis when no column has strictly negative
;; reduced cost is not proved here.
(def pricing-converged-spec
  {:name 'column-generation/pricing-converged :universes []
   :type (equality bool (worth-adding? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (worth-adding? (whole 7) (whole 5)))})

(def theorem-specs
  [prices-favorably-spec added-column-improves-spec pricing-converged-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-column-generation
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
