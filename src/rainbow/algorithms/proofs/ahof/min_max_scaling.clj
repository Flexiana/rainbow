(ns rainbow.algorithms.proofs.ahof.min-max-scaling
  "AHoF Min-Max Scaling (normalization): rescale a feature linearly to the unit
  interval [0, 1] by mapping the minimum to 0 and the maximum to 1,

      scaled offset range = (x - min) / (max - min),

  where offset = x - min and range = max - min. Unlike z-score standardization it
  bounds every value into [0, 1] (useful for image pixels, neural-net inputs, and
  bounded activations), at the cost of sensitivity to outliers. Proved native and
  axiom-free: the scaled value as exact rational division of the offset by the
  range; a worked scaling; and that the maximum (offset = range) maps to 1. The
  min, max, and offset computations are executable; what is proved is the
  normalizing division.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.min-max-scaling`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

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

(defn- scaled [offset range]
  (function/app (function/const* 'min-max-scaling/scaled []) offset range))

;; Definitions --------------------------------------------------------------

;; scaled offset range = offset / range
(def scaled-spec
  {:name 'min-max-scaling/scaled :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['offset nnrat] ['range nnrat]]
                        (nnrat-divide 'offset 'range))})

(def definition-specs [scaled-spec])

;; Theorems -----------------------------------------------------------------

;; Offset 3 (x - min), range 4 (max - min) -> scaled 3/4.
(def scaled-example-spec
  {:name 'min-max-scaling/scaled-example :universes []
   :type (nnrat-equivalent (scaled (whole 3) (whole 4)) (fraction 3 3))
   :value (equivalent-proof (scaled (whole 3) (whole 4)) (fraction 3 3))})

;; The maximum value (offset = range = 4) maps to 1.
(def maximum-maps-to-one-spec
  {:name 'min-max-scaling/maximum-maps-to-one :universes []
   :type (nnrat-equivalent (scaled (whole 4) (whole 4)) (whole 1))
   :value (equivalent-proof (scaled (whole 4) (whole 4)) (whole 1))})

(def theorem-specs [scaled-example-spec maximum-maps-to-one-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-min-max-scaling (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.min-max-scaling))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
