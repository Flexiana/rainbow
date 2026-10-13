(ns rainbow.algorithms.proofs.ahof.reinforce
  "AHoF D46 REINFORCE (likelihood-ratio policy gradient): the Monte-Carlo policy
  gradient estimator weights each sampled trajectory's score-function by its
  return. The estimate is the (mean of the) sum of return times score over the
  sampled trajectories:

      estimate r1 s1 r2 s2 = r1 * s1 + r2 * s2

  over exact nonnegative rationals (two trajectories; the general estimator folds
  this over the batch and divides by the count). The trajectory returns and the
  score-function values grad log pi are problem/executable data supplied as
  rationals; the division by the batch size for the mean is executable. What is
  proved here is the deterministic return-weighted score combination and worked
  instances that reduce by reflexivity on the exact rational arithmetic.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.reinforce`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- estimate [r1 s1 r2 s2]
  (function/app (function/const* 'reinforce/estimate []) r1 s1 r2 s2))

;; Definitions --------------------------------------------------------------

;; estimate r1 s1 r2 s2 = r1*s1 + r2*s2
(def estimate-spec
  {:name 'reinforce/estimate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['r1 nnrat] ['s1 nnrat] ['r2 nnrat] ['s2 nnrat]]
                        (nnrat-add (nnrat-multiply 'r1 's1)
                                   (nnrat-multiply 'r2 's2)))})

(def definition-specs [estimate-spec])

;; Theorems -----------------------------------------------------------------

(def estimate-unfold-spec
  {:name 'reinforce/estimate-unfold :universes []
   :type (function/forall
          [['r1 nnrat] ['s1 nnrat] ['r2 nnrat] ['s2 nnrat]]
          (equality nnrat
                    (estimate 'r1 's1 'r2 's2)
                    (nnrat-add (nnrat-multiply 'r1 's1)
                               (nnrat-multiply 'r2 's2))))
   :value (function/lam [['r1 nnrat] ['s1 nnrat] ['r2 nnrat] ['s2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (estimate 'r1 's1 'r2 's2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked estimate: returns (2,1), scores (3,4) -> 2*3 + 1*4 = 10.
(def estimate-example-spec
  {:name 'reinforce/estimate-example :universes []
   :type (equality nnrat
                   (estimate (whole 2) (whole 3) (whole 1) (whole 4))
                   (whole 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (estimate (whole 2) (whole 3) (whole 1) (whole 4)))})

;; A zero-return trajectory contributes nothing: returns (0,1), scores (9,4) ->
;; 0*9 + 1*4 = 4 (high-score but zero-return trajectory is ignored).
(def zero-return-ignored-spec
  {:name 'reinforce/zero-return-ignored :universes []
   :type (equality nnrat
                   (estimate (whole 0) (whole 9) (whole 1) (whole 4))
                   (whole 4))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (estimate (whole 0) (whole 9) (whole 1) (whole 4)))})

(def theorem-specs
  [estimate-unfold-spec estimate-example-spec zero-return-ignored-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-reinforce
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
