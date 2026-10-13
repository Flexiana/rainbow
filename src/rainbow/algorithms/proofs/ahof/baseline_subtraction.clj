(ns rainbow.algorithms.proofs.ahof.baseline-subtraction
  "AHoF D48 Baseline Subtraction: the variance-reduction wrapper for
  policy-gradient estimators. Subtracting a state-dependent baseline from the
  return before weighting the score leaves the gradient unbiased but reduces its
  variance. The baselined per-trajectory contribution weights the score by the
  ADVANTAGE (return minus baseline):

      contribution advantage score = advantage * score

  over exact nonnegative rationals, where the advantage = return - baseline is
  supplied (its sign handling and the optimal-baseline choice are executable).
  Proved native and axiom-free: the contribution unfolds to advantage * score for
  all advantages and scores, and two worked instances (3 * 4 = 12, and a zero
  advantage 0 * 9 = 0) that reduce by reflexivity on the exact arithmetic.
  Unbiasedness and variance reduction are the classical properties of the
  baseline; they are not proved here.

  Requires nnrat/multiply and nnrat/at-most (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.baseline-subtraction`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- contribution [advantage score]
  (function/app (function/const* 'baseline/contribution []) advantage score))

;; Definitions --------------------------------------------------------------

;; contribution advantage score = advantage * score
(def contribution-spec
  {:name 'baseline/contribution :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['advantage nnrat] ['score nnrat]]
                        (nnrat-multiply 'advantage 'score))})

(def definition-specs [contribution-spec])

;; Theorems -----------------------------------------------------------------

(def contribution-unfold-spec
  {:name 'baseline/contribution-unfold :universes []
   :type (function/forall
          [['advantage nnrat] ['score nnrat]]
          (equality nnrat
                    (contribution 'advantage 'score)
                    (nnrat-multiply 'advantage 'score)))
   :value (function/lam [['advantage nnrat] ['score nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (contribution 'advantage 'score)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def rational-zero (function/const* 'nnrat/zero []))

;; Worked contribution: advantage 3, score 4 -> 12.
(def contribution-example-spec
  {:name 'baseline/contribution-example :universes []
   :type (equality nnrat (contribution (whole 3) (whole 4)) (whole 12))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (contribution (whole 3) (whole 4)))})

;; Worked zero advantage: 0 * 9 = 0.
(def zero-advantage-cancels-spec
  {:name 'baseline/zero-advantage-cancels :universes []
   :type (equality nnrat (contribution rational-zero (whole 9)) rational-zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (contribution rational-zero (whole 9)))})

(def theorem-specs
  [contribution-unfold-spec contribution-example-spec
   zero-advantage-cancels-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-baseline-subtraction (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.baseline-subtraction))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
