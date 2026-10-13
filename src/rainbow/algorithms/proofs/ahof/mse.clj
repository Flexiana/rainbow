(ns rainbow.algorithms.proofs.ahof.mse
  "AHoF Mean Squared Error: the standard loss for regression and the objective of
  least-squares fitting -- the average of the squared prediction errors,

      squared-error e = e * e
      mse e0 e1       = (e0*e0 + e1*e1) / 2      (a two-sample average).

  Squaring penalizes large errors quadratically and makes the loss smooth and
  convex in the predictions (for a linear model), which is why its gradient drives
  least-squares and neural-network training. Proved native and axiom-free: the
  squared-error term; a worked squared error; the two-sample mean squared error
  composing squares, a sum, and exact rational division; and a worked MSE. The
  residual (y - y_hat) computation is executable; what is proved is the squared
  error and its average.

  Requires nnrat/multiply, nnrat/add, nnrat/divide (division is the
  rational-division capability, composed here), and the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mse`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- squared-error [e]
  (function/app (function/const* 'mse/squared-error []) e))
(defn- mse [e0 e1]
  (function/app (function/const* 'mse/mse []) e0 e1))

;; Definitions --------------------------------------------------------------

;; squared-error e = e * e
(def squared-error-spec
  {:name 'mse/squared-error :kind :definition :universes []
   :type (function/arrow nnrat nnrat)
   :value (function/lam [['e nnrat]] (nnrat-multiply 'e 'e))})

;; mse e0 e1 = (e0*e0 + e1*e1) / 2
(def mse-spec
  {:name 'mse/mse :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['e0 nnrat] ['e1 nnrat]]
                        (nnrat-divide
                         (nnrat-add (nnrat-multiply 'e0 'e0)
                                    (nnrat-multiply 'e1 'e1))
                         (whole 2)))})

(def definition-specs [squared-error-spec mse-spec])

;; Theorems -----------------------------------------------------------------

;; Squared error of a residual 3 is 9.
(def squared-error-example-spec
  {:name 'mse/squared-error-example :universes []
   :type (equality nnrat (squared-error (whole 3)) (whole 9))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (squared-error (whole 3)))})

;; MSE of residuals 2 and 1: (4 + 1) / 2 = 5/2.
(def mse-example-spec
  {:name 'mse/mse-example :universes []
   :type (equality nnrat (mse (whole 2) (whole 1)) (fraction 5 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (mse (whole 2) (whole 1)))})

;; A perfect fit (zero residuals) has zero loss.
(def perfect-fit-zero-loss-spec
  {:name 'mse/perfect-fit-zero-loss :universes []
   :type (equality nnrat (squared-error (whole 0)) (whole 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (squared-error (whole 0)))})

(def theorem-specs
  [squared-error-example-spec mse-example-spec perfect-fit-zero-loss-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-mse
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
