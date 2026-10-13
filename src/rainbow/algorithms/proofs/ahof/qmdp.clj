(ns rainbow.algorithms.proofs.ahof.qmdp
  "AHoF D22 QMDP (POMDP planning approximation): approximate the value of an
  action under partial observability by weighting the fully-observable Q-values
  by the current belief over states,

      qmdp-value b0 q0 b1 q1 = b0 * Q(s0, a) + b1 * Q(s1, a)

  (a two-state belief; the general form sums over all states). QMDP acts as if all
  uncertainty resolves after one step -- cheap and often effective. Proved native
  and axiom-free: the belief-weighted value; a worked value (stated as rational
  equivalence via the cross-product certificate, since the mixed weights yield a
  non-lowest-terms pair); and that under a certain belief (b0 = 1) the value
  reduces to the single state's Q-value -- reducing by reflexivity. The
  underlying MDP Q-values and the belief update are executable; what is proved is
  the belief-weighted value combination.

  Requires nnrat/add, nnrat/multiply, nnrat/equivalent (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.qmdp`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
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

(defn- qmdp-value [b0 q0 b1 q1]
  (function/app (function/const* 'qmdp/value []) b0 q0 b1 q1))

;; Definitions --------------------------------------------------------------

;; qmdp-value b0 q0 b1 q1 = b0*q0 + b1*q1
(def value-spec
  {:name 'qmdp/value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['q0 nnrat] ['b1 nnrat] ['q1 nnrat]]
                        (nnrat-add (nnrat-multiply 'b0 'q0)
                                   (nnrat-multiply 'b1 'q1)))})

(def definition-specs [value-spec])

;; Theorems -----------------------------------------------------------------

;; Belief (1/2, 1/2) over states with Q-values (1, 3): value 2.
(def value-example-spec
  {:name 'qmdp/value-example :universes []
   :type (nnrat-equivalent
          (qmdp-value (fraction 1 1) (whole 1) (fraction 1 1) (whole 3))
          (whole 2))
   :value (equivalent-proof
           (qmdp-value (fraction 1 1) (whole 1) (fraction 1 1) (whole 3))
           (whole 2))})

;; Certain belief (b0 = 1, b1 = 0): the value is exactly the known state's
;; Q-value (QMDP reduces to the MDP under no uncertainty).
(def certain-belief-spec
  {:name 'qmdp/certain-belief :universes []
   :type (nnrat-equivalent
          (qmdp-value (whole 1) (whole 5) (whole 0) (whole 9))
          (whole 5))
   :value (equivalent-proof
           (qmdp-value (whole 1) (whole 5) (whole 0) (whole 9))
           (whole 5))})

(def theorem-specs [value-example-spec certain-belief-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-qmdp
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
