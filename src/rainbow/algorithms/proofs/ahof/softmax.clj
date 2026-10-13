(ns rainbow.algorithms.proofs.ahof.softmax
  "AHoF Softmax: turn a vector of real-valued scores (logits) into a probability
  distribution over classes -- the standard output layer of multi-class
  classifiers and the policy head of policy-gradient RL. Each class probability is
  its exponentiated score divided by the sum of all exponentiated scores:

      softmax-share exp-score total-exp = exp-score / total-exp

  so the shares are classically non-negative and sum to one. Proved native and
  axiom-free: the softmax share as exact rational division of the score's
  exponential by the normalizer; a worked share 3 / 4 = 3/4; and the worked sum
  3/4 + 1/4 = 1 of two complementary shares. The exponentials (a transcendental)
  are executable / supplied. That the shares sum to one for all inputs is not
  proved here.

  Requires nnrat/divide (rational-division capability, composed here), nnrat/add,
  nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.softmax`
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
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- softmax-share [exp-score total-exp]
  (function/app (function/const* 'softmax/share []) exp-score total-exp))

;; Definitions --------------------------------------------------------------

;; softmax-share exp-score total-exp = exp-score / total-exp
(def share-spec
  {:name 'softmax/share :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['exp-score nnrat] ['total-exp nnrat]]
                        (nnrat-divide 'exp-score 'total-exp))})

(def definition-specs [share-spec])

;; Theorems -----------------------------------------------------------------

;; A class with exp-score 3 out of total 4 gets probability 3/4.
(def share-example-spec
  {:name 'softmax/share-example :universes []
   :type (nnrat-equivalent (softmax-share (whole 3) (whole 4)) (fraction 3 3))
   :value (equivalent-proof (softmax-share (whole 3) (whole 4)) (fraction 3 3))})

;; Worked sum: shares 3/4 and 1/4 of a two-class softmax sum to 1.
(def shares-sum-to-one-spec
  {:name 'softmax/shares-sum-to-one :universes []
   :type (nnrat-equivalent
          (nnrat-add (softmax-share (whole 3) (whole 4))
                     (softmax-share (whole 1) (whole 4)))
          (whole 1))
   :value (equivalent-proof
           (nnrat-add (softmax-share (whole 3) (whole 4))
                      (softmax-share (whole 1) (whole 4)))
           (whole 1))})

(def theorem-specs [share-example-spec shares-sum-to-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-softmax
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
