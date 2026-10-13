(ns rainbow.algorithms.proofs.ahof.perceptron
  "AHoF Perceptron (Rosenblatt): the foundational linear classifier and the atom
  of neural networks. It predicts a class from the sign of a weighted sum of
  inputs (the activation) relative to a threshold, and learns by the mistake-driven
  rule w <- w + eta*(y - y_hat)*x, which -- by the perceptron convergence theorem
  -- finds a separating hyperplane in finitely many updates when the data are
  linearly separable. The firing (activation) decision is:

      fires? activation threshold = decide (threshold <= activation)

  over exact-rational activations. Proved native and axiom-free: the firing test
  and worked instances on concrete values -- activation 3 against threshold 2
  fires; the worked certificate 2 <= 3 as a native nnrat/at-most; and activation
  1 against threshold 2 does not fire. The weight vector, the update rule, and
  the dot product are executable; what is proved is the firing decision at these
  instances. The perceptron convergence theorem is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.perceptron`
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
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- fires? [activation threshold]
  (function/app (function/const* 'perceptron/fires? []) activation threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; fires? activation threshold = decide (threshold <= activation)
(def fires-spec
  {:name 'perceptron/fires? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['activation nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'activation))})

(def definition-specs [fires-spec])

;; Theorems -----------------------------------------------------------------

;; An activation 3 reaching threshold 2 fires (predicts the positive class).
(def activation-fires-spec
  {:name 'perceptron/activation-fires :universes []
   :type (equality bool (fires? (whole 3) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (fires? (whole 3) (whole 2)))})

;; Worked certificate: threshold 2 <= activation 3.
(def firing-meets-threshold-spec
  {:name 'perceptron/firing-meets-threshold :universes []
   :type (nnrat-at-most (whole 2) (whole 3))
   :value (at-most-proof (whole 2) (whole 3))})

;; A sub-threshold activation (1 < threshold 2) does not fire (negative class).
(def subthreshold-does-not-fire-spec
  {:name 'perceptron/subthreshold-does-not-fire :universes []
   :type (equality bool (fires? (whole 1) (whole 2))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (fires? (whole 1) (whole 2)))})

(def theorem-specs
  [activation-fires-spec firing-meets-threshold-spec
   subthreshold-does-not-fire-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-perceptron
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
