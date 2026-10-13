(ns rainbow.algorithms.proofs.penalty-method
  "AHoF O48 Penalty Method: the transform that turns a constrained problem into
  an unconstrained one by folding a penalty on constraint violation into the
  objective:

      augmented(x) = objective(x) + rho * penalty(x)

  where rho is the penalty weight and penalty(x) measures constraint violation
  (zero when feasible). This is exact-rational multiplication and addition; the
  constraint functions and the outer schedule that grows rho are the executable
  concern. What is proved is the augmented-objective recurrence and worked
  instances: with a feasible point (penalty 0) the augmented value equals the
  objective, and an infeasible point adds the weighted violation.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.penalty-method`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- augmented [objective rho penalty]
  (function/app (function/const* 'penalty/augmented []) objective rho penalty))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; augmented = objective + rho * penalty
(def augmented-spec
  {:name 'penalty/augmented :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['objective nnrat] ['rho nnrat] ['penalty nnrat]]
                        (add 'objective (multiply 'rho 'penalty)))})

(def definition-specs [augmented-spec])

;; Theorems -----------------------------------------------------------------

(def augmented-unfold-spec
  {:name 'penalty/augmented-unfold :universes []
   :type (function/forall
          [['objective nnrat] ['rho nnrat] ['penalty nnrat]]
          (equality nnrat (augmented 'objective 'rho 'penalty)
                    (add 'objective (multiply 'rho 'penalty))))
   :value (function/lam [['objective nnrat] ['rho nnrat] ['penalty nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (augmented 'objective 'rho 'penalty)))})

;; An infeasible point: objective 1, weight 2, violation 3 -> 1 + 2*3 = 7.
(def infeasible-example-spec
  {:name 'penalty/infeasible-example :universes []
   :type (equivalent (augmented (whole 1) (whole 2) (whole 3)) (whole 7))
   :value (cross-product-reflexivity
           (augmented (whole 1) (whole 2) (whole 3)) (whole 7))})

;; A feasible point (penalty 0): the augmented value equals the objective.
(def feasible-example-spec
  {:name 'penalty/feasible-example :universes []
   :type (equivalent (augmented (whole 5) (whole 2) (whole 0)) (whole 5))
   :value (cross-product-reflexivity
           (augmented (whole 5) (whole 2) (whole 0)) (whole 5))})

(def theorem-specs [augmented-unfold-spec infeasible-example-spec
                    feasible-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :penalty-method
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
