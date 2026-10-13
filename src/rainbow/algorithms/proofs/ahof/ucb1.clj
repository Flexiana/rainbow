(ns rainbow.algorithms.proofs.ahof.ucb1
  "AHoF D57 UCB1 (bandit arm selection): pull the arm with the largest upper-
  confidence-bound score UCB_i = mean_i + sqrt(2 ln t / n_i). With two arms the
  policy keeps the larger score and prefers arm 0 when its UCB is at least arm 1's:

      prefers-arm-zero? u0 u1 = decide (u1 <= u0)
      best-score u0 u1        = if (u1 <= u0) then u0 else u1   (the larger UCB)

  over exact rationals (the UCB eliminator over nnrat). Proved native and axiom-free:
  the preference decision, the best-score selection, a worked selection, and that the
  preference flips when arm 1's score is larger. Requires audit/decide-nnrat-at-most,
  logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ucb1`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

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

(defn- prefers-arm-zero? [u0 u1]
  (function/app (function/const* 'ucb1/prefers-arm-zero? []) u0 u1))
(defn- best-score [u0 u1]
  (function/app (function/const* 'ucb1/best-score []) u0 u1))

;; prefers-arm-zero? u0 u1 = decide (u1 <= u0)
(def prefers-spec
  {:name 'ucb1/prefers-arm-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]] (decide-at-most 'u1 'u0))})

;; best-score u0 u1 = if (u1 <= u0) then u0 else u1  (the larger UCB)
(def best-score-spec
  {:name 'ucb1/best-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'u1 'u0))
                                      (decide-at-most 'u1 'u0) 'u0 'u1))})

(def definition-specs [prefers-spec best-score-spec])

;; With scores 3/4 (arm 0) and 1/2 (arm 1), arm 0 is preferred.
(def prefers-higher-arm-spec
  {:name 'ucb1/prefers-higher-arm :universes []
   :type (equality bool (prefers-arm-zero? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-arm-zero? (fraction 3 3) (fraction 1 1)))})

;; ...and the best score kept is 3/4.
(def selects-higher-value-spec
  {:name 'ucb1/selects-higher-value :universes []
   :type (equality nnrat (best-score (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-score (fraction 3 3) (fraction 1 1)))})

;; When arm 1's score 3/4 exceeds arm 0's 1/2, arm 0 is no longer preferred.
(def switches-when-lower-spec
  {:name 'ucb1/switches-when-lower :universes []
   :type (equality bool (prefers-arm-zero? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-arm-zero? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [prefers-higher-arm-spec selects-higher-value-spec switches-when-lower-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-ucb1 (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.ucb1))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
