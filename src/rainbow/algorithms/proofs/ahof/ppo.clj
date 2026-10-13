(ns rainbow.algorithms.proofs.ahof.ppo
  "AHoF D43 Proximal Policy Optimization: a policy-gradient method that keeps
  updates in a trust region by CLIPPING the probability ratio r = pi_new/pi_old
  into [1 - eps, 1 + eps] before forming the surrogate objective. Clipping
  removes the incentive to move the ratio outside the interval; it is meant to give
  stable improvement without a hard KL constraint (an empirical motivation, not a
  property proved here). The clip is a clamp:

      ppo-clip r lo hi = max(lo, min(r, hi))

  built from the decidable rational min and max (each = if a<=b then .. else ..
  over logic/if-data). Proved native and axiom-free: the clip; a ratio above the
  band clamped down to hi; a ratio below the band clamped up to lo; and an
  in-band ratio passed through unchanged -- all reducing by reflexivity. The
  advantage estimates and gradient step are executable; what is proved is the
  clipping clamp.

  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ppo`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nnrat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- nnrat-min [a b]
  (function/app (function/const* 'ppo/nnrat-min []) a b))
(defn- nnrat-max [a b]
  (function/app (function/const* 'ppo/nnrat-max []) a b))
(defn- ppo-clip [r lo hi]
  (function/app (function/const* 'ppo/clip []) r lo hi))

;; Definitions --------------------------------------------------------------

;; nnrat-min a b = if (a <= b) then a else b
(def nnrat-min-spec
  {:name 'ppo/nnrat-min :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (if-nnrat (decide-at-most 'a 'b) 'a 'b))})

;; nnrat-max a b = if (a <= b) then b else a
(def nnrat-max-spec
  {:name 'ppo/nnrat-max :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (if-nnrat (decide-at-most 'a 'b) 'b 'a))})

;; ppo-clip r lo hi = max(lo, min(r, hi)) -- clamp r into [lo, hi]
(def clip-spec
  {:name 'ppo/clip :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['r nnrat] ['lo nnrat] ['hi nnrat]]
                        (nnrat-max 'lo (nnrat-min 'r 'hi)))})

(def definition-specs [nnrat-min-spec nnrat-max-spec clip-spec])

;; Theorems -----------------------------------------------------------------

;; Trust band [3/4, 5/4] (eps = 1/4).
(def lo (fraction 3 3))   ; 3/4
(def hi (fraction 5 3))   ; 5/4

;; A ratio 3/2 above the band is clamped down to hi = 5/4.
(def clips-above-to-hi-spec
  {:name 'ppo/clips-above-to-hi :universes []
   :type (equality nnrat (ppo-clip (fraction 3 1) lo hi) hi)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ppo-clip (fraction 3 1) lo hi))})

;; A ratio 1/2 below the band is clamped up to lo = 3/4.
(def clips-below-to-lo-spec
  {:name 'ppo/clips-below-to-lo :universes []
   :type (equality nnrat (ppo-clip (fraction 1 1) lo hi) lo)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ppo-clip (fraction 1 1) lo hi))})

;; An in-band ratio 1 passes through unchanged.
(def passes-in-band-spec
  {:name 'ppo/passes-in-band :universes []
   :type (equality nnrat (ppo-clip (fraction 1 0) lo hi) (fraction 1 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ppo-clip (fraction 1 0) lo hi))})

(def theorem-specs
  [clips-above-to-hi-spec clips-below-to-lo-spec passes-in-band-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-ppo
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
