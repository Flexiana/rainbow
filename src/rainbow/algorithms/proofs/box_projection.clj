(ns rainbow.algorithms.proofs.box-projection
  "AHoF box projection (the projection step of Projected Gradient Descent and
  box-constrained optimization): after an unconstrained gradient step lands at x,
  the iterate is projected back onto the feasible box [lo, hi] by clamping,

      clamp lo hi x = max(lo, min(x, hi))

  using the decidable rational order. The projection is designed to keep every
  iterate in the box (lo <= clamp lo hi x <= hi); that is NOT proved here for all
  inputs. The gradient step itself is an executable concern; what is proved here
  is the clamp operation and worked instances on the box [2, 8]: clamp 5 = 5
  (identity inside), clamp 10 = 8 and clamp 1 = 2 (saturation at the active
  bound), and feasibility of those two, clamp 10 <= 8 and 2 <= clamp 1.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all carried by the D63
  checkpoint).

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.box-projection`
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))

;; nnrat-min a b = if (a <= b) then a else b ; nnrat-max a b = if (a <= b) then b else a
(defn- nnrat-min-term [a b] (if-value (decide-at-most a b) a b))
(defn- nnrat-max-term [a b] (if-value (decide-at-most a b) b a))

(defn- clamp [lo hi x]
  (function/app (function/const* 'projection/clamp []) lo hi x))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; clamp lo hi x = max(lo, min(x, hi))  (project x onto the box [lo, hi])
(def clamp-spec
  {:name 'projection/clamp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['lo nnrat] ['hi nnrat] ['x nnrat]]
                        (nnrat-max-term 'lo (nnrat-min-term 'x 'hi)))})

(def definition-specs [clamp-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Inside the box the projection is the identity: clamp [2,8] 5 = 5.
(def clamp-inside-spec
  {:name 'projection/clamp-inside :universes []
   :type (equality nnrat (clamp (whole 2) (whole 8) (whole 5)) (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (whole 2) (whole 8) (whole 5)))})

;; Above the box it saturates at the upper bound: clamp [2,8] 10 = 8.
(def clamp-above-spec
  {:name 'projection/clamp-above :universes []
   :type (equality nnrat (clamp (whole 2) (whole 8) (whole 10)) (whole 8))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (whole 2) (whole 8) (whole 10)))})

;; Below the box it saturates at the lower bound: clamp [2,8] 1 = 2.
(def clamp-below-spec
  {:name 'projection/clamp-below :universes []
   :type (equality nnrat (clamp (whole 2) (whole 8) (whole 1)) (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (clamp (whole 2) (whole 8) (whole 1)))})

;; Feasibility (upper), worked instance: clamp [2,8] 10 <= 8.
(def clamp-below-hi-spec
  {:name 'projection/clamp-below-hi :universes []
   :type (nnrat-at-most (clamp (whole 2) (whole 8) (whole 10)) (whole 8))
   :value (at-most-proof (clamp (whole 2) (whole 8) (whole 10)) (whole 8))})

;; Feasibility (lower), worked instance: 2 <= clamp [2,8] 1.
(def clamp-above-lo-spec
  {:name 'projection/clamp-above-lo :universes []
   :type (nnrat-at-most (whole 2) (clamp (whole 2) (whole 8) (whole 1)))
   :value (at-most-proof (whole 2) (clamp (whole 2) (whole 8) (whole 1)))})

(def theorem-specs
  [clamp-inside-spec clamp-above-spec clamp-below-spec
   clamp-below-hi-spec clamp-above-lo-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :box-projection (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.box-projection))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
