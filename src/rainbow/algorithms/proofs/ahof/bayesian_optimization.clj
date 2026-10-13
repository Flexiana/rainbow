(ns rainbow.algorithms.proofs.ahof.bayesian-optimization
  "AHoF O65 Bayesian Optimization Loop: iterate (fit surrogate -> maximize
  acquisition -> evaluate) and track the best observation seen. The loop's
  bookkeeping core is the incumbent update -- after evaluating a new
  candidate the best-so-far is the better of the old incumbent and the new value
  (maximization):

      update-incumbent best candidate = max(best, candidate)

  over the decidable rational order. Proved native and axiom-free: the incumbent
  update and a worked step with best 5 and candidate 8 -- the update adopts 8,
  5 <= update 5 8, and 8 <= update 5 8. The general max inequalities, and that
  the best value is nondecreasing across iterations, are not proved here.
  Surrogate fitting (RBF/GP), acquisition
  maximization (EI/UCB), and the objective evaluation are executable / separately
  proved concerns; what is proved here is the incumbent bookkeeping.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayesian-optimization`
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
;; max a b = if (a <= b) then b else a
(defn- nnrat-max-term [a b] (if-value (decide-at-most a b) b a))

(defn- update-incumbent [best candidate]
  (function/app (function/const* 'bayesopt/update-incumbent []) best candidate))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; update-incumbent best candidate = max(best, candidate)
(def update-incumbent-spec
  {:name 'bayesopt/update-incumbent :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['best nnrat] ['candidate nnrat]]
                        (nnrat-max-term 'best 'candidate))})

(def definition-specs [update-incumbent-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A better candidate advances the incumbent (best 5, candidate 8 -> 8).
(def adopts-better-candidate-spec
  {:name 'bayesopt/adopts-better-candidate :universes []
   :type (equality nnrat (update-incumbent (whole 5) (whole 8)) (whole 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (update-incumbent (whole 5) (whole 8)))})

;; Worked step: the incumbent does not regress (5 <= update 5 8).
(def incumbent-never-regresses-spec
  {:name 'bayesopt/incumbent-never-regresses :universes []
   :type (nnrat-at-most (whole 5) (update-incumbent (whole 5) (whole 8)))
   :value (at-most-proof (whole 5) (update-incumbent (whole 5) (whole 8)))})

;; The incumbent dominates the newest candidate (8 <= 8).
(def incumbent-dominates-candidate-spec
  {:name 'bayesopt/incumbent-dominates-candidate :universes []
   :type (nnrat-at-most (whole 8) (update-incumbent (whole 5) (whole 8)))
   :value (at-most-proof (whole 8) (update-incumbent (whole 5) (whole 8)))})

(def theorem-specs
  [adopts-better-candidate-spec incumbent-never-regresses-spec
   incumbent-dominates-candidate-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bayesian-optimization
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
