(ns rainbow.algorithms.proofs.ahof.precision-recall
  "AHoF Precision and Recall: the two complementary quality metrics of a binary
  classifier, computed from the confusion-matrix counts (true/false positives and
  negatives),

      precision tp fp = tp / (tp + fp)     (of predicted positives, how many are right)
      recall    tp fn = tp / (tp + fn)     (of actual positives, how many are found).

  Precision penalizes false alarms; recall penalizes misses; the trade-off between
  them (tuned by the decision threshold) is the basis of the precision-recall curve
  and F1. Proved native and axiom-free: precision and recall as exact rational
  divisions of the true-positive count by predicted-positives and
  actual-positives respectively; worked values; and that a classifier with no false
  positives has precision 1. The confusion-matrix tallies are executable; what is
  proved is the precision/recall fractions.

  Requires nnrat/add, nnrat/divide (division is the rational-division capability,
  composed here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.precision-recall`
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

(defn- precision [tp fp]
  (function/app (function/const* 'precision-recall/precision []) tp fp))
(defn- recall [tp fn]
  (function/app (function/const* 'precision-recall/recall []) tp fn))

;; Definitions --------------------------------------------------------------

;; precision tp fp = tp / (tp + fp)
(def precision-spec
  {:name 'precision-recall/precision :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['tp nnrat] ['fp nnrat]]
                        (nnrat-divide 'tp (nnrat-add 'tp 'fp)))})

;; recall tp fn = tp / (tp + fn)
(def recall-spec
  {:name 'precision-recall/recall :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['tp nnrat] ['fn nnrat]]
                        (nnrat-divide 'tp (nnrat-add 'tp 'fn)))})

(def definition-specs [precision-spec recall-spec])

;; Theorems -----------------------------------------------------------------

;; TP=3, FP=1 -> precision 3/4.
(def precision-example-spec
  {:name 'precision-recall/precision-example :universes []
   :type (nnrat-equivalent (precision (whole 3) (whole 1)) (fraction 3 3))
   :value (equivalent-proof (precision (whole 3) (whole 1)) (fraction 3 3))})

;; TP=3, FN=2 -> recall 3/5.
(def recall-example-spec
  {:name 'precision-recall/recall-example :universes []
   :type (nnrat-equivalent (recall (whole 3) (whole 2)) (fraction 3 4))
   :value (equivalent-proof (recall (whole 3) (whole 2)) (fraction 3 4))})

;; No false positives (FP=0) -> precision 1.
(def no-false-positives-precision-one-spec
  {:name 'precision-recall/no-false-positives-precision-one :universes []
   :type (nnrat-equivalent (precision (whole 5) (whole 0)) (whole 1))
   :value (equivalent-proof (precision (whole 5) (whole 0)) (whole 1))})

(def theorem-specs
  [precision-example-spec recall-example-spec
   no-false-positives-precision-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-precision-recall
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
