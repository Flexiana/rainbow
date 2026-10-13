(ns rainbow.algorithms.proofs.ahof.kernel-smoothing
  "AHoF D26 Kernel Smoothing value-function approximation: approximate the value
  at a query state by a kernel-weighted average of the stored sample values, with
  weights given by a similarity kernel. The unnormalized estimate (numerator) is
  the kernel-weighted sum of sample values:

      weighted-sum k1 v1 k2 v2 = k1 * v1 + k2 * v2

  and the normalizer is the kernel weight total k1 + k2; the value estimate is
  their ratio (a division, executable). Proved native and axiom-free over exact
  rationals: the kernel-weighted numerator and the weight-total normalizer, with
  worked instances that reduce by reflexivity. The similarity kernel
  k(s, s_i) = exp(-||s - s_i||^2 / h) is transcendental and executable -- its
  VALUES are supplied as rationals. What is proved here is the deterministic
  weighting arithmetic.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kernel-smoothing`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- weighted-sum [k1 v1 k2 v2]
  (function/app (function/const* 'kernel-smoothing/weighted-sum []) k1 v1 k2 v2))
(defn- weight-total [k1 k2]
  (function/app (function/const* 'kernel-smoothing/weight-total []) k1 k2))

;; Definitions --------------------------------------------------------------

;; weighted-sum k1 v1 k2 v2 = k1*v1 + k2*v2  (numerator of the estimate)
(def weighted-sum-spec
  {:name 'kernel-smoothing/weighted-sum :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['k1 nnrat] ['v1 nnrat] ['k2 nnrat] ['v2 nnrat]]
                        (nnrat-add (nnrat-multiply 'k1 'v1)
                                   (nnrat-multiply 'k2 'v2)))})

;; weight-total k1 k2 = k1 + k2  (normalizer / denominator)
(def weight-total-spec
  {:name 'kernel-smoothing/weight-total :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['k1 nnrat] ['k2 nnrat]] (nnrat-add 'k1 'k2))})

(def definition-specs [weighted-sum-spec weight-total-spec])

;; Theorems -----------------------------------------------------------------

(def weighted-sum-unfold-spec
  {:name 'kernel-smoothing/weighted-sum-unfold :universes []
   :type (function/forall
          [['k1 nnrat] ['v1 nnrat] ['k2 nnrat] ['v2 nnrat]]
          (equality nnrat
                    (weighted-sum 'k1 'v1 'k2 'v2)
                    (nnrat-add (nnrat-multiply 'k1 'v1)
                               (nnrat-multiply 'k2 'v2))))
   :value (function/lam [['k1 nnrat] ['v1 nnrat] ['k2 nnrat] ['v2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (weighted-sum 'k1 'v1 'k2 'v2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked numerator: kernels (2,1), values (3,4) -> 2*3 + 1*4 = 10.
(def weighted-sum-example-spec
  {:name 'kernel-smoothing/weighted-sum-example :universes []
   :type (equality nnrat
                   (weighted-sum (whole 2) (whole 3) (whole 1) (whole 4))
                   (whole 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (weighted-sum (whole 2) (whole 3) (whole 1) (whole 4)))})

;; Worked normalizer: kernel weights 2 and 1 total 3 (so the estimate is 10/3).
(def weight-total-example-spec
  {:name 'kernel-smoothing/weight-total-example :universes []
   :type (equality nnrat (weight-total (whole 2) (whole 1)) (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (weight-total (whole 2) (whole 1)))})

(def theorem-specs
  [weighted-sum-unfold-spec weighted-sum-example-spec weight-total-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-kernel-smoothing
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
