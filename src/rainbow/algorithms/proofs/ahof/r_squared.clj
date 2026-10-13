(ns rainbow.algorithms.proofs.ahof.r-squared
  "AHoF R-squared (coefficient of determination): summarize how well a regression
  fits by the FRACTION of the total variance in the target that the model
  explains,

      r-squared explained-variance total-variance = explained-variance / total-variance
        = SS_regression / SS_total = 1 - SS_residual / SS_total.

  It ranges in [0, 1] for a least-squares fit: 1 means the model explains all
  variance (perfect fit), 0 means it does no better than predicting the mean.
  Proved native and axiom-free: R-squared as exact rational division of explained
  by total variance; a worked value; and that a model explaining all the variance
  (explained = total) has R-squared = 1. The sum-of-squares computations are
  executable; what is proved is the explained-variance fraction.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.r-squared`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- r-squared [explained-variance total-variance]
  (function/app (function/const* 'r-squared/r-squared []) explained-variance total-variance))

;; Definitions --------------------------------------------------------------

;; r-squared explained total = explained / total
(def r-squared-spec
  {:name 'r-squared/r-squared :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['explained-variance nnrat] ['total-variance nnrat]]
                        (nnrat-divide 'explained-variance 'total-variance))})

(def definition-specs [r-squared-spec])

;; Theorems -----------------------------------------------------------------

;; Explained variance 3, total variance 4 -> R-squared 3/4 (75% explained).
(def r-squared-example-spec
  {:name 'r-squared/r-squared-example :universes []
   :type (nnrat-equivalent (r-squared (whole 3) (whole 4)) (fraction 3 3))
   :value (equivalent-proof (r-squared (whole 3) (whole 4)) (fraction 3 3))})

;; A perfect fit (explained = total = 5) has R-squared = 1.
(def perfect-fit-r-squared-one-spec
  {:name 'r-squared/perfect-fit-r-squared-one :universes []
   :type (nnrat-equivalent (r-squared (whole 5) (whole 5)) (whole 1))
   :value (equivalent-proof (r-squared (whole 5) (whole 5)) (whole 1))})

(def theorem-specs [r-squared-example-spec perfect-fit-r-squared-one-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-r-squared (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.r-squared))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
