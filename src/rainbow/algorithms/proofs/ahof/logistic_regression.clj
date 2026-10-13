(ns rainbow.algorithms.proofs.ahof.logistic-regression
  "AHoF Logistic Regression: a probabilistic linear classifier that models the
  class probability as the logistic sigmoid of a linear score,
  P(y=1|x) = sigmoid(w.x + b), trained by maximizing the log-likelihood (gradient
  ascent). At prediction time a point is labelled positive when its predicted
  probability reaches the decision threshold (1/2 by default, equivalently the
  linear score reaching 0):

      classify-positive? probability threshold = decide (threshold <= probability)

  over exact-rational probabilities. Proved native and axiom-free: the
  classification decision; that a probability at least 1/2 is labelled positive;
  the certificate that a positive label really means probability >= threshold
  (native nnrat/at-most) -- calibrated by the threshold; and that a probability
  below 1/2 is labelled negative. The sigmoid, the log-likelihood gradient, and the
  weight updates are executable; what is proved is the probability-threshold
  decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.logistic-regression`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- classify-positive? [probability threshold]
  (function/app (function/const* 'logistic/classify-positive? [])
                probability threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; classify-positive? probability threshold = decide (threshold <= probability)
(def classify-positive-spec
  {:name 'logistic/classify-positive? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['probability nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'probability))})

(def definition-specs [classify-positive-spec])

;; Theorems -----------------------------------------------------------------

;; A predicted probability of 3/4 (>= threshold 1/2) is labelled positive.
(def high-probability-positive-spec
  {:name 'logistic/high-probability-positive :universes []
   :type (equality bool (classify-positive? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (classify-positive? (fraction 3 3) (fraction 1 1)))})

;; Certificate: a positive label means the probability met the threshold
;; (1/2 <= 3/4).
(def positive-meets-threshold-spec
  {:name 'logistic/positive-meets-threshold :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; A predicted probability of 1/4 (below threshold 1/2) is labelled negative.
(def low-probability-negative-spec
  {:name 'logistic/low-probability-negative :universes []
   :type (equality bool (classify-positive? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (classify-positive? (fraction 1 3) (fraction 1 1)))})

(def theorem-specs
  [high-probability-positive-spec positive-meets-threshold-spec
   low-probability-negative-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-logistic-regression
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
