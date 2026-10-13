(ns rainbow.algorithms.proofs.ahof.accuracy
  "AHoF Classification Accuracy: the simplest evaluation metric -- the fraction of
  predictions that are correct,

      accuracy correct total = correct / total,

  a value in [0, 1]. It is the go-to score on balanced data (though misleading on
  imbalanced classes, where F1 or balanced accuracy are preferred). Defined:
  accuracy as exact rational division of the correct count by the total. Proved
  native and axiom-free, as worked instances: 3 correct of 4 gives accuracy 3/4,
  and 5 correct of 5 gives accuracy 1. That correct = total gives accuracy 1 for
  every total is not proved here. The prediction/label comparison is executable.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.accuracy`
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

(defn- accuracy [correct total]
  (function/app (function/const* 'accuracy/accuracy []) correct total))

;; Definitions --------------------------------------------------------------

;; accuracy correct total = correct / total
(def accuracy-spec
  {:name 'accuracy/accuracy :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['correct nnrat] ['total nnrat]]
                        (nnrat-divide 'correct 'total))})

(def definition-specs [accuracy-spec])

;; Theorems -----------------------------------------------------------------

;; 3 correct of 4 -> accuracy 3/4.
(def accuracy-example-spec
  {:name 'accuracy/accuracy-example :universes []
   :type (nnrat-equivalent (accuracy (whole 3) (whole 4)) (fraction 3 3))
   :value (equivalent-proof (accuracy (whole 3) (whole 4)) (fraction 3 3))})

;; A classifier correct on every example (correct = total = 5) has accuracy 1.
(def perfect-classifier-accuracy-one-spec
  {:name 'accuracy/perfect-classifier-accuracy-one :universes []
   :type (nnrat-equivalent (accuracy (whole 5) (whole 5)) (whole 1))
   :value (equivalent-proof (accuracy (whole 5) (whole 5)) (whole 1))})

(def theorem-specs [accuracy-example-spec perfect-classifier-accuracy-one-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-accuracy (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.accuracy))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
