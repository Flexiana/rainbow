(ns rainbow.algorithms.proofs.ahof.ols-regression
  "AHoF Ordinary Least Squares (simple linear regression): fit a line y = slope*x +
  intercept minimizing the sum of squared residuals. Setting the gradient of the
  squared-error loss to zero gives the CLOSED FORM: the slope is the covariance of
  x and y divided by the variance of x,

      slope covariance variance = covariance / variance

  and the intercept then centres the line through the means. This is the unique
  minimizer (the loss is convex), so no iteration is needed. Proved native and
  axiom-free: the slope as exact rational division of covariance by variance; a
  worked slope; and that when covariance equals variance the slope is 1 (x and y
  move together one-for-one). The covariance and variance computations (which need
  centred sums) are executable; what is proved is the normal-equation slope.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ols-regression`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- nnrat-equivalent [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- numerator-of [v]
  (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator-of [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-multiply [a b]
  (function/app (function/const* 'nat/multiply []) a b))
(defn- equivalent-proof [a b]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (nat-multiply (numerator-of a) (denominator-of b))))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- slope [covariance variance]
  (function/app (function/const* 'ols/slope []) covariance variance))

;; Definitions --------------------------------------------------------------

;; slope covariance variance = covariance / variance
(def slope-spec
  {:name 'ols/slope :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['covariance nnrat] ['variance nnrat]]
                        (nnrat-divide 'covariance 'variance))})

(def definition-specs [slope-spec])

;; Theorems -----------------------------------------------------------------

;; Covariance 3, variance 2 -> slope 3/2.
(def slope-example-spec
  {:name 'ols/slope-example :universes []
   :type (nnrat-equivalent (slope (whole 3) (whole 2)) (fraction 3 1))
   :value (equivalent-proof (slope (whole 3) (whole 2)) (fraction 3 1))})

;; When covariance equals variance, the slope is 1 (x and y move one-for-one).
(def unit-covariance-slope-one-spec
  {:name 'ols/unit-covariance-slope-one :universes []
   :type (nnrat-equivalent (slope (whole 2) (whole 2)) (whole 1))
   :value (equivalent-proof (slope (whole 2) (whole 2)) (whole 1))})

(def theorem-specs [slope-example-spec unit-covariance-slope-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-ols-regression
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
