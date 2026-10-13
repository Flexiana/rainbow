(ns rainbow.algorithms.proofs.ahof.neural-vf
  "AHoF D30 Neural Network Value Function: approximate the value function with a
  trainable neural network. The forward pass of a single linear-layer neuron
  (pre-activation) is the weighted sum of its inputs plus a bias:

      neuron w1 x1 w2 x2 b = w1*x1 + w2*x2 + b

  over exact nonnegative rationals (two inputs; the general neuron folds the
  weighted sum over all inputs). Proved native and axiom-free: the neuron
  pre-activation, and the guarantee that the pre-activation is at least the bias
  (b <= neuron) when the weighted inputs are nonnegative, so a nonnegative-weight
  layer never falls below its bias floor. The nonlinear activation (ReLU / tanh),
  the multi-layer composition, and gradient-descent training are executable
  concerns; the weights and bias are supplied rationals. What is proved here is
  the deterministic linear pre-activation.

  Requires nnrat/add, nnrat/multiply, nnrat/at-most, and the decidable nnrat
  order (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.neural-vf`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- neuron [w1 x1 w2 x2 b]
  (function/app (function/const* 'neural-vf/neuron []) w1 x1 w2 x2 b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; neuron w1 x1 w2 x2 b = w1*x1 + w2*x2 + b
(def neuron-spec
  {:name 'neural-vf/neuron :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w1 nnrat] ['x1 nnrat] ['w2 nnrat] ['x2 nnrat]
                         ['b nnrat]]
                        (nnrat-add
                         (nnrat-add (nnrat-multiply 'w1 'x1)
                                    (nnrat-multiply 'w2 'x2))
                         'b))})

(def definition-specs [neuron-spec])

;; Theorems -----------------------------------------------------------------

(def neuron-unfold-spec
  {:name 'neural-vf/neuron-unfold :universes []
   :type (function/forall
          [['w1 nnrat] ['x1 nnrat] ['w2 nnrat] ['x2 nnrat] ['b nnrat]]
          (equality nnrat
                    (neuron 'w1 'x1 'w2 'x2 'b)
                    (nnrat-add
                     (nnrat-add (nnrat-multiply 'w1 'x1)
                                (nnrat-multiply 'w2 'x2))
                     'b)))
   :value (function/lam [['w1 nnrat] ['x1 nnrat] ['w2 nnrat] ['x2 nnrat]
                         ['b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (neuron 'w1 'x1 'w2 'x2 'b)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked pre-activation: weights (2,1), inputs (3,4), bias 5 -> 2*3+1*4+5 = 15.
(def neuron-example-spec
  {:name 'neural-vf/neuron-example :universes []
   :type (equality nnrat
                   (neuron (whole 2) (whole 3) (whole 1) (whole 4) (whole 5))
                   (whole 15))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (neuron (whole 2) (whole 3) (whole 1) (whole 4)
                                (whole 5)))})

;; Bias floor: with nonnegative weighted inputs the pre-activation is at least
;; the bias (5 <= 15).
(def neuron-above-bias-spec
  {:name 'neural-vf/neuron-above-bias :universes []
   :type (nnrat-at-most (whole 5)
                        (neuron (whole 2) (whole 3) (whole 1) (whole 4)
                                (whole 5)))
   :value (at-most-proof (whole 5)
                         (neuron (whole 2) (whole 3) (whole 1) (whole 4)
                                 (whole 5)))})

(def theorem-specs
  [neuron-unfold-spec neuron-example-spec neuron-above-bias-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-neural-vf (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.neural-vf))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
