(ns rainbow.algorithms.proofs.ahof.kalman
  "AHoF D-family Kalman Filter: the optimal linear estimator for a
  Gaussian-linear system, alternating a predict step (propagate mean and
  variance) and an update step that fuses a noisy measurement. With prior
  variance P and measurement-noise variance R, the scalar update is governed by
  the Kalman gain and the posterior variance:

      kalman-gain P R      = P / (P + R)
      kalman-posterior P R = P * R / (P + R)     ( = (1 - gain) * P )

  over exact rationals (both defined here). Proved native and axiom-free, as
  worked instances reducing by reflexivity via exact rational division: a
  balanced fusion (P = R = 1 gives gain 1/2 and posterior 1/2) and a
  confident-measurement case (P = 3, R = 1 gives gain 3/4). The filter's
  optimality, and that the gain grows as R shrinks for all inputs, are classical
  properties not proved here. The measurement, the process model, and the mean
  update (which needs signed innovation) are executable.

  Requires nnrat/divide, nnrat/add, nnrat/multiply (division is the
  rational-division capability, composed here; the rest are in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kalman`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- kalman-gain [p r]
  (function/app (function/const* 'kalman/gain []) p r))
(defn- kalman-posterior [p r]
  (function/app (function/const* 'kalman/posterior []) p r))

;; Definitions --------------------------------------------------------------

;; kalman-gain P R = P / (P + R)
(def gain-spec
  {:name 'kalman/gain :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p nnrat] ['r nnrat]]
                        (nnrat-divide 'p (nnrat-add 'p 'r)))})

;; kalman-posterior P R = (P * R) / (P + R)
(def posterior-spec
  {:name 'kalman/posterior :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p nnrat] ['r nnrat]]
                        (nnrat-divide (nnrat-multiply 'p 'r)
                                      (nnrat-add 'p 'r)))})

(def definition-specs [gain-spec posterior-spec])

;; Theorems -----------------------------------------------------------------

;; Balanced fusion P = R = 1: gain 1/2 (equal trust in prior and measurement).
(def balanced-gain-spec
  {:name 'kalman/balanced-gain :universes []
   :type (equality nnrat (kalman-gain (whole 1) (whole 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (kalman-gain (whole 1) (whole 1)))})

;; Balanced fusion posterior variance 1/2 (uncertainty halved by the fusion).
(def balanced-posterior-spec
  {:name 'kalman/balanced-posterior :universes []
   :type (equality nnrat (kalman-posterior (whole 1) (whole 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (kalman-posterior (whole 1) (whole 1)))})

;; Confident measurement (P = 3, R = 1): larger gain 3/4 -- trust the measurement
;; more when its noise is small relative to the prior.
(def confident-measurement-gain-spec
  {:name 'kalman/confident-measurement-gain :universes []
   :type (equality nnrat (kalman-gain (whole 3) (whole 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (kalman-gain (whole 3) (whole 1)))})

(def theorem-specs
  [balanced-gain-spec balanced-posterior-spec confident-measurement-gain-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-kalman (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.kalman))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
