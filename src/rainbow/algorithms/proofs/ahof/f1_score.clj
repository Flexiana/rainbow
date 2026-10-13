(ns rainbow.algorithms.proofs.ahof.f1-score
  "AHoF F1 Score: the standard single-number summary of a classifier's quality on
  imbalanced data -- the HARMONIC MEAN of precision and recall,

      f1 precision recall = 2 * precision * recall / (precision + recall).

  The harmonic mean is high only when BOTH precision and recall are high (it is
  dominated by the smaller of the two), unlike the arithmetic mean, which is why
  F1 resists being gamed by a classifier that trades one metric for the other.
  Proved native and axiom-free: the F1 combination (composing nnrat/multiply,
  nnrat/add, and exact rational division); a worked F1 (stated as rational
  equivalence via the cross-product certificate); and that a perfect classifier
  (precision = recall = 1) has F1 = 1. The confusion-matrix counts (TP, FP, FN)
  and precision/recall are executable; what is proved is the harmonic-mean
  combination.

  Requires nnrat/multiply, nnrat/add, nnrat/divide (division is the
  rational-division capability, composed here), nnrat/equivalent, and the D63
  checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.f1-score`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
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

(defn- f1 [precision recall]
  (function/app (function/const* 'f1-score/f1 []) precision recall))

;; Definitions --------------------------------------------------------------

;; f1 precision recall = 2 * precision * recall / (precision + recall)
(def f1-spec
  {:name 'f1-score/f1 :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['precision nnrat] ['recall nnrat]]
                        (nnrat-divide
                         (nnrat-multiply (whole 2)
                                         (nnrat-multiply 'precision 'recall))
                         (nnrat-add 'precision 'recall)))})

(def definition-specs [f1-spec])

;; Theorems -----------------------------------------------------------------

;; Precision 3/4, recall 1/2: F1 = 2*(3/8)/(5/4) = (3/4)/(5/4) = 3/5.
(def f1-example-spec
  {:name 'f1-score/f1-example :universes []
   :type (nnrat-equivalent (f1 (fraction 3 3) (fraction 1 1)) (fraction 3 4))
   :value (equivalent-proof (f1 (fraction 3 3) (fraction 1 1)) (fraction 3 4))})

;; A perfect classifier (precision = recall = 1) has F1 = 1.
(def perfect-classifier-f1-one-spec
  {:name 'f1-score/perfect-classifier-f1-one :universes []
   :type (nnrat-equivalent (f1 (whole 1) (whole 1)) (whole 1))
   :value (equivalent-proof (f1 (whole 1) (whole 1)) (whole 1))})

(def theorem-specs [f1-example-spec perfect-classifier-f1-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-f1-score
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
