(ns rainbow.algorithms.proofs.ahof.rbf-surrogate
  "AHoF O61 Radial Basis Function surrogate: an interpolating surrogate model that
  predicts by a weighted sum of radial basis functions centered at the sampled
  points. With basis-function evaluations phi_i at the query and fitted weights
  w_i, the prediction is the weighted sum (shown for two centers; the general
  case folds this over all centers):

      predict w1 phi1 w2 phi2 = w1 * phi1 + w2 * phi2

  over exact nonnegative rationals. The radial kernel phi(r) = exp(-(r/l)^2) (or
  a multiquadric with a square root) is transcendental and stays an executable
  concern -- its VALUES are supplied as rationals; the fitted weights come from
  solving the interpolation system, also executable. What is proved here is the
  deterministic prediction combination and worked instances that reduce by
  reflexivity on the exact rational arithmetic.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rbf-surrogate`
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

(defn- predict [w1 phi1 w2 phi2]
  (function/app (function/const* 'rbf/predict []) w1 phi1 w2 phi2))

;; Definitions --------------------------------------------------------------

;; predict w1 phi1 w2 phi2 = w1 * phi1 + w2 * phi2
(def predict-spec
  {:name 'rbf/predict :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w1 nnrat] ['phi1 nnrat] ['w2 nnrat] ['phi2 nnrat]]
                        (nnrat-add (nnrat-multiply 'w1 'phi1)
                                   (nnrat-multiply 'w2 'phi2)))})

(def definition-specs [predict-spec])

;; Theorems -----------------------------------------------------------------

(def predict-unfold-spec
  {:name 'rbf/predict-unfold :universes []
   :type (function/forall
          [['w1 nnrat] ['phi1 nnrat] ['w2 nnrat] ['phi2 nnrat]]
          (equality nnrat
                    (predict 'w1 'phi1 'w2 'phi2)
                    (nnrat-add (nnrat-multiply 'w1 'phi1)
                               (nnrat-multiply 'w2 'phi2))))
   :value (function/lam [['w1 nnrat] ['phi1 nnrat] ['w2 nnrat] ['phi2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (predict 'w1 'phi1 'w2 'phi2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked prediction: weights (2,1), basis values (3,4) -> 2*3 + 1*4 = 10.
(def predict-example-spec
  {:name 'rbf/predict-example :universes []
   :type (equality nnrat
                   (predict (whole 2) (whole 3) (whole 1) (whole 4))
                   (whole 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (predict (whole 2) (whole 3) (whole 1) (whole 4)))})

;; Interpolation sanity: a single active basis (second weight 0) returns its own
;; contribution -- weights (2,0), values (3,4) -> 2*3 + 0*4 = 6.
(def predict-single-basis-spec
  {:name 'rbf/predict-single-basis :universes []
   :type (equality nnrat
                   (predict (whole 2) (whole 3) (whole 0) (whole 4))
                   (whole 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (predict (whole 2) (whole 3) (whole 0) (whole 4)))})

(def theorem-specs
  [predict-unfold-spec predict-example-spec predict-single-basis-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-rbf-surrogate
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
