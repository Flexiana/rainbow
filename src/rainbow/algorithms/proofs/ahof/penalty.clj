(ns rainbow.algorithms.proofs.ahof.penalty
  "AHoF O-family Penalty Method: solve a constrained optimization problem by a
  sequence of UNCONSTRAINED problems whose objective adds a penalty proportional
  to the constraint violation,

      penalized f mu violation = f + mu * violation

  where mu is the penalty coefficient (increased across outer iterations). As mu
  grows, minimizers are driven toward feasibility; at a feasible point the penalty
  vanishes and the penalized objective equals the true objective. Proved native
  and axiom-free: the penalized-objective combination; a worked penalized value;
  and that at zero violation (a feasible point) the penalized objective equals the
  original objective -- reducing by reflexivity. The base objective and the
  constraint-violation measure are executable; what is proved is the penalized
  objective combination.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.penalty`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- penalized [f mu violation]
  (function/app (function/const* 'penalty/penalized []) f mu violation))

;; Definitions --------------------------------------------------------------

;; penalized f mu violation = f + mu * violation
(def penalized-spec
  {:name 'penalty/penalized :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['f nnrat] ['mu nnrat] ['violation nnrat]]
                        (nnrat-add 'f (nnrat-multiply 'mu 'violation)))})

(def definition-specs [penalized-spec])

;; Theorems -----------------------------------------------------------------

;; Worked: objective 2, penalty coefficient 3, violation 1 -> penalized 5.
(def penalized-example-spec
  {:name 'penalty/penalized-example :universes []
   :type (equality nnrat
                   (penalized (whole 2) (whole 3) (whole 1))
                   (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (penalized (whole 2) (whole 3) (whole 1)))})

;; At a feasible point (violation 0), the penalty vanishes: penalized = objective.
(def feasible-equals-objective-spec
  {:name 'penalty/feasible-equals-objective :universes []
   :type (equality nnrat
                   (penalized (whole 2) (whole 3) (whole 0))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (penalized (whole 2) (whole 3) (whole 0)))})

(def theorem-specs [penalized-example-spec feasible-equals-objective-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-penalty (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.penalty))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
