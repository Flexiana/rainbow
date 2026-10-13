(ns rainbow.algorithms.proofs.ahof.gradient-boosting
  "AHoF Gradient Boosting (GBM / the core of XGBoost, LightGBM): build a strong
  predictor as an additive ensemble, where each stage fits a weak learner (usually
  a shallow tree) to the negative gradient of the loss (the residuals) and adds a
  SHRUNKEN version of it to the running model:

      boost-update current learning-rate weak = current + learning-rate * weak

  The learning rate (shrinkage) < 1 regularizes, trading more boosting rounds for
  better generalization. Proved native and axiom-free: the additive update; a
  worked boosting step; and that at learning rate 0 the model is unchanged (no
  learning) -- reducing by reflexivity. The weak-learner fit and the residual /
  gradient computation are executable; what is proved is the shrunken additive
  update.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gradient-boosting`
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
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- boost-update [current learning-rate weak]
  (function/app (function/const* 'gradient-boosting/update []) current learning-rate weak))

;; Definitions --------------------------------------------------------------

;; boost-update current learning-rate weak = current + learning-rate * weak
(def update-spec
  {:name 'gradient-boosting/update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['current nnrat] ['learning-rate nnrat] ['weak nnrat]]
                        (nnrat-add 'current
                                   (nnrat-multiply 'learning-rate 'weak)))})

(def definition-specs [update-spec])

;; Theorems -----------------------------------------------------------------

;; A boosting step: model 2, learning rate 1/2, weak learner 1 -> 5/2.
(def boost-step-example-spec
  {:name 'gradient-boosting/boost-step-example :universes []
   :type (equality nnrat
                   (boost-update (whole 2) (fraction 1 1) (whole 1))
                   (fraction 5 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (boost-update (whole 2) (fraction 1 1) (whole 1)))})

;; At learning rate 0, the ensemble is unchanged (no learning this round).
(def zero-rate-unchanged-spec
  {:name 'gradient-boosting/zero-rate-unchanged :universes []
   :type (equality nnrat
                   (boost-update (whole 3) (whole 0) (whole 9))
                   (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (boost-update (whole 3) (whole 0) (whole 9)))})

(def theorem-specs [boost-step-example-spec zero-rate-unchanged-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-gradient-boosting (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.gradient-boosting))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
