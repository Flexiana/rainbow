(ns rainbow.algorithms.proofs.ahof.clamped-surrogate
  "AHoF D52 Clamped Surrogate Objective (PPO): stabilize policy-gradient updates by
  clamping the probability ratio r into the trust region [lo, hi] = [1-eps, 1+eps]
  before forming the surrogate objective:

      clamp r lo hi = min (max r lo) hi.

  A ratio 3/4 already inside [1/2, 1] clamps to itself; a ratio 1/4 below the region
  clamps up to the lower edge 1/2; a ratio 2 above the region clamps down to the upper
  edge 1. Proved native and axiom-free: the clamp (nested min/max) and the three
  worked regimes (inside, below, above). Requires audit/decide-nnrat-at-most,
  logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.clamped-surrogate`
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
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

;; max a b = if (a <= b) then b else a
(defn- max-term [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition (decide-at-most a b)) (decide-at-most a b) b a))
;; min a b = if (a <= b) then a else b
(defn- min-term [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition (decide-at-most a b)) (decide-at-most a b) a b))

(defn- clamp [r lo hi]
  (function/app (function/const* 'clip/clamp []) r lo hi))

;; clamp r lo hi = min (max r lo) hi
(def clamp-spec
  {:name 'clip/clamp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['r nnrat] ['lo nnrat] ['hi nnrat]]
                        (min-term (max-term 'r 'lo) 'hi))})

(def definition-specs [clamp-spec])

;; A ratio 3/4 inside [1/2, 1] clamps to itself.
(def inside-region-unchanged-spec
  {:name 'clip/inside-region-unchanged :universes []
   :type (equality nnrat (clamp (fraction 3 3) (fraction 1 1) (whole 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (fraction 3 3) (fraction 1 1) (whole 1)))})

;; A ratio 1/4 below the region clamps up to the lower edge 1/2.
(def below-region-clamped-up-spec
  {:name 'clip/below-region-clamped-up :universes []
   :type (equality nnrat (clamp (fraction 1 3) (fraction 1 1) (whole 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (fraction 1 3) (fraction 1 1) (whole 1)))})

;; A ratio 2 above the region clamps down to the upper edge 1.
(def above-region-clamped-down-spec
  {:name 'clip/above-region-clamped-down :universes []
   :type (equality nnrat (clamp (whole 2) (fraction 1 1) (whole 1)) (whole 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (whole 2) (fraction 1 1) (whole 1)))})

(def theorem-specs
  [inside-region-unchanged-spec below-region-clamped-up-spec
   above-region-clamped-down-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-clamped-surrogate (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.clamped-surrogate))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
