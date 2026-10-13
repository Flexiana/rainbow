(ns rainbow.algorithms.proofs.ahof.frank-wolfe
  "AHoF O-family Frank-Wolfe (Conditional Gradient) method: minimize a convex
  objective over a convex set WITHOUT projections. Each iterate solves a linear
  subproblem for a vertex s (the linear-minimization oracle), then moves toward
  it by a convex combination with step gamma in [0,1]:

      x' = (1 - gamma) x + gamma s.

  Because x and s are both feasible and the update is a convex combination, x'
  stays feasible -- the projection-free property. Written with the complementary
  weights w0 = 1 - gamma and w1 = gamma (w0 + w1 = 1):

      fw-step x s w0 w1 = w0 * x + w1 * s

  over exact rationals. Proved native and axiom-free: the convex-combination
  step; a worked half-step; that a full step (w0=0, w1=1) jumps to the vertex s;
  and that a null step (w0=1, w1=0) stays at x -- all reducing by reflexivity.
  The gradient and the linear-minimization oracle are executable; what is proved
  is the convex-combination update.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.frank-wolfe`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- fw-step [x s w0 w1]
  (function/app (function/const* 'frank-wolfe/step []) x s w0 w1))
(def nat (function/const* 'data/Nat []))
(defn- nnrat-equivalent [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- numerator-of [v]
  (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator-of [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-multiply [a b]
  (function/app (function/const* 'nat/multiply []) a b))
;; Cross-product equivalence witness: a ~ b since num(a)*den(b) = num(b)*den(a).
(defn- equivalent-proof [a b]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (nat-multiply (numerator-of a) (denominator-of b))))

;; Definitions --------------------------------------------------------------

;; fw-step x s w0 w1 = w0 * x + w1 * s  (convex combination, w0 + w1 = 1)
(def step-spec
  {:name 'frank-wolfe/step :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['x nnrat] ['s nnrat] ['w0 nnrat] ['w1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 'x)
                                   (nnrat-multiply 'w1 's)))})

(def definition-specs [step-spec])

;; Theorems -----------------------------------------------------------------

;; Half step from x=2 toward vertex s=0 (gamma = 1/2) lands at 1 (the combined
;; weights produce a non-lowest-terms pair equivalent to 1, so this is stated as
;; rational equivalence via the cross-product certificate).
(def half-step-spec
  {:name 'frank-wolfe/half-step :universes []
   :type (nnrat-equivalent
          (fw-step (whole 2) (whole 0) (fraction 1 1) (fraction 1 1))
          (whole 1))
   :value (equivalent-proof
           (fw-step (whole 2) (whole 0) (fraction 1 1) (fraction 1 1))
           (whole 1))})

;; Full step (gamma = 1, w0 = 0, w1 = 1) jumps to the vertex s.
(def full-step-to-vertex-spec
  {:name 'frank-wolfe/full-step-to-vertex :universes []
   :type (equality nnrat
                   (fw-step (whole 2) (whole 7) (whole 0) (whole 1))
                   (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (fw-step (whole 2) (whole 7) (whole 0) (whole 1)))})

;; Null step (gamma = 0, w0 = 1, w1 = 0) stays at x.
(def null-step-stays-spec
  {:name 'frank-wolfe/null-step-stays :universes []
   :type (equality nnrat
                   (fw-step (whole 2) (whole 7) (whole 1) (whole 0))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (fw-step (whole 2) (whole 7) (whole 1) (whole 0)))})

(def theorem-specs
  [half-step-spec full-step-to-vertex-spec null-step-stays-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-frank-wolfe
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
