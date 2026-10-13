(ns rainbow.algorithms.proofs.ahof.z-score
  "AHoF Z-Score Standardization: rescale a feature to zero mean and unit standard
  deviation, z = (x - mean) / std-dev -- the standard preprocessing step that puts
  features on a comparable scale (essential for distance-based methods, gradient
  descent conditioning, and regularization) and expresses each value as a number of
  standard deviations from the mean. Writing the (absolute) deviation d = |x - mean|:

      z-score deviation std-dev = deviation / std-dev

  over exact rationals. Proved native and axiom-free: the z-score as exact rational
  division of the deviation by the standard deviation; a worked z-score; and that a
  value exactly one standard deviation from the mean has |z| = 1. The mean, the
  standard deviation, and the sign of the deviation are executable; what is proved
  is the standardizing division.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.z-score`
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

(defn- z-score [deviation std-dev]
  (function/app (function/const* 'z-score/z-score []) deviation std-dev))

;; Definitions --------------------------------------------------------------

;; z-score deviation std-dev = deviation / std-dev
(def z-score-spec
  {:name 'z-score/z-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['deviation nnrat] ['std-dev nnrat]]
                        (nnrat-divide 'deviation 'std-dev))})

(def definition-specs [z-score-spec])

;; Theorems -----------------------------------------------------------------

;; Deviation 3, standard deviation 2 -> z-score 3/2 (1.5 standard deviations out).
(def z-score-example-spec
  {:name 'z-score/z-score-example :universes []
   :type (nnrat-equivalent (z-score (whole 3) (whole 2)) (fraction 3 1))
   :value (equivalent-proof (z-score (whole 3) (whole 2)) (fraction 3 1))})

;; A value exactly one standard deviation from the mean has |z| = 1.
(def one-sigma-z-one-spec
  {:name 'z-score/one-sigma-z-one :universes []
   :type (nnrat-equivalent (z-score (whole 2) (whole 2)) (whole 1))
   :value (equivalent-proof (z-score (whole 2) (whole 2)) (whole 1))})

(def theorem-specs [z-score-example-spec one-sigma-z-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-z-score
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
