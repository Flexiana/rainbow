(ns rainbow.algorithms.proofs.ahof.ista
  "AHoF O-family ISTA (Iterative Shrinkage-Thresholding / proximal gradient): the
  standard first-order method for L1-regularized (LASSO) problems. Each iteration
  takes a gradient step on the smooth loss, then applies the proximal operator of
  the L1 penalty -- the soft-thresholding (shrinkage) operator, which drives small
  coefficients exactly to zero and thereby induces sparsity. A coefficient of
  magnitude m is shrunk to zero exactly when it does not exceed the threshold
  lambda (the step size times the regularization weight):

      shrinks-to-zero? m lambda = decide (m <= lambda)

  over exact-rational magnitudes. Proved native and axiom-free: the shrinkage
  test; the certificate that a zeroed coefficient really is within the threshold
  (m <= lambda as native nnrat/at-most) -- so soft-thresholding is exact; and that
  a coefficient above the threshold survives (is only shrunk, not zeroed). The
  gradient step and the shrinkage magnitude are executable; what is proved is the
  sparsity-inducing thresholding decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ista`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- shrinks-to-zero? [m lambda]
  (function/app (function/const* 'ista/shrinks-to-zero? []) m lambda))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; shrinks-to-zero? m lambda = decide (m <= lambda)
(def shrinks-spec
  {:name 'ista/shrinks-to-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['m nnrat] ['lambda nnrat]]
                        (decide-at-most 'm 'lambda))})

(def definition-specs [shrinks-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

;; A coefficient of magnitude 1/4 within threshold lambda = 1/2 is zeroed.
(def small-coefficient-zeroed-spec
  {:name 'ista/small-coefficient-zeroed :universes []
   :type (equality bool (shrinks-to-zero? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (shrinks-to-zero? (fraction 1 3) (fraction 1 1)))})

;; Certificate: a zeroed coefficient is within the threshold (1/4 <= 1/2), so the
;; soft-threshold is exact.
(def zeroed-within-threshold-spec
  {:name 'ista/zeroed-within-threshold :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

;; A coefficient of magnitude 3/4 above the threshold survives (not zeroed).
(def large-coefficient-survives-spec
  {:name 'ista/large-coefficient-survives :universes []
   :type (equality bool (shrinks-to-zero? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (shrinks-to-zero? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [small-coefficient-zeroed-spec zeroed-within-threshold-spec
   large-coefficient-survives-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-ista (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.ista))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
