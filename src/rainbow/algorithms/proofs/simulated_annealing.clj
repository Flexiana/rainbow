(ns rainbow.algorithms.proofs.simulated-annealing
  "AHoF O40 Simulated Annealing: the geometric temperature schedule and the
  deterministic (greedy-limit) Metropolis acceptance. The temperature cools by a
  constant rational factor each iteration, `T' = alpha * T` (exact nonnegative
  rational multiplication), and a candidate is accepted when it does not worsen
  the cost, `accept? = candidate-cost <= current-cost` (the decidable rational
  comparison).

  This reuses the exact-rational arithmetic and decidable comparison engines
  rather than the vector cone, so its structure is a scalar schedule plus a
  decision, not a vector update. The full Metropolis criterion accepts an uphill
  move with probability exp(-delta / T); that exponential is not exact-rational,
  so the probabilistic branch stays an executable-only concern and what is proved
  here is the cooling schedule and the deterministic acceptance.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.simulated-annealing`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))

(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- cool [alpha temperature]
  (function/app (function/const* 'annealing/cool []) alpha temperature))
(defn- accept-better? [candidate current]
  (function/app (function/const* 'annealing/accept-better? []) candidate current))

;; Definitions --------------------------------------------------------------

;; T' = alpha * T
(def cool-spec
  {:name 'annealing/cool :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['alpha nnrat] ['temperature nnrat]]
                        (nnrat-multiply 'alpha 'temperature))})

;; accept? = candidate-cost <= current-cost  (greedy-limit Metropolis)
(def accept-better?-spec
  {:name 'annealing/accept-better? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['candidate nnrat] ['current nnrat]]
                        (decide-at-most 'candidate 'current))})

(def definition-specs [cool-spec accept-better?-spec])

;; Theorems -----------------------------------------------------------------

(def cool-unfold-spec
  {:name 'annealing/cool-unfold :universes []
   :type (function/forall
          [['alpha nnrat] ['temperature nnrat]]
          (equality nnrat (cool 'alpha 'temperature)
                    (nnrat-multiply 'alpha 'temperature)))
   :value (function/lam [['alpha nnrat] ['temperature nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (cool 'alpha 'temperature)))})

(def accept-unfold-spec
  {:name 'annealing/accept-unfold :universes []
   :type (function/forall
          [['candidate nnrat] ['current nnrat]]
          (equality bool (accept-better? 'candidate 'current)
                    (decide-at-most 'candidate 'current)))
   :value (function/lam [['candidate nnrat] ['current nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (accept-better? 'candidate 'current)))})

;; Worked schedule and acceptance -------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
;; nnrat/make takes (numerator, denominator-PREDECESSOR), so predecessor 0 gives
;; denominator 1: (whole n) is the integer cost n as the rational n/1.
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(def true-term (function/const* 'data/true []))
(def false-term (function/const* 'data/false []))

;; A cheaper candidate (cost 1) is accepted over a costlier current (cost 2).
(def accept-better-example-spec
  {:name 'annealing/accept-better-example :universes []
   :type (equality bool (accept-better? (whole 1) (whole 2)) true-term)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accept-better? (whole 1) (whole 2)))})

;; A costlier candidate (cost 2) is rejected against a cheaper current (cost 1).
(def reject-worse-example-spec
  {:name 'annealing/reject-worse-example :universes []
   :type (equality bool (accept-better? (whole 2) (whole 1)) false-term)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accept-better? (whole 2) (whole 1)))})

(def theorem-specs
  [cool-unfold-spec accept-unfold-spec
   accept-better-example-spec reject-worse-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :simulated-annealing (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.simulated-annealing))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
