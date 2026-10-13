(ns rainbow.algorithms.proofs.ahof.linear-regression-vf
  "AHoF D29 Linear Regression Value Function: approximate the value function as a
  linear combination of state features, V(s) = w . phi(s). The prediction is the
  weighted sum of the feature values by the fitted weights:

      predict w1 f1 w2 f2 = w1*f1 + w2*f2

  over exact nonnegative rationals (two features; the general case folds over the
  feature vector). Proved native and axiom-free: the linear prediction and worked
  instances that reduce by reflexivity. The feature map phi (a supplied HOF from
  states to feature vectors) and the least-squares / TD weight fit are executable
  concerns; the weights and feature values are supplied rationals. What is proved
  here is the deterministic linear combination.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 1 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.linear-regression-vf`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- predict [w1 f1 w2 f2]
  (function/app (function/const* 'linear-vf/predict []) w1 f1 w2 f2))

;; Definitions --------------------------------------------------------------

;; predict w1 f1 w2 f2 = w1*f1 + w2*f2
(def predict-spec
  {:name 'linear-vf/predict :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
                        (nnrat-add (nnrat-multiply 'w1 'f1)
                                   (nnrat-multiply 'w2 'f2)))})

(def definition-specs [predict-spec])

;; Theorems -----------------------------------------------------------------

(def predict-unfold-spec
  {:name 'linear-vf/predict-unfold :universes []
   :type (function/forall
          [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
          (equality nnrat
                    (predict 'w1 'f1 'w2 'f2)
                    (nnrat-add (nnrat-multiply 'w1 'f1)
                               (nnrat-multiply 'w2 'f2))))
   :value (function/lam [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (predict 'w1 'f1 'w2 'f2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked prediction: weights (2,1), features (3,4) -> 2*3 + 1*4 = 10.
(def predict-example-spec
  {:name 'linear-vf/predict-example :universes []
   :type (equality nnrat
                   (predict (whole 2) (whole 3) (whole 1) (whole 4))
                   (whole 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (predict (whole 2) (whole 3) (whole 1) (whole 4)))})

(def theorem-specs [predict-unfold-spec predict-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-linear-regression-vf (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.linear-regression-vf))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
