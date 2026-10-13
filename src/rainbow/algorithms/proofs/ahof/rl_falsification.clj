(ns rainbow.algorithms.proofs.ahof.rl-falsification
  "AHoF V20 RL for Falsification: train an agent by reinforcement learning to drive the
  system toward a specification violation, acting greedily on the learned Q-values by
  keeping the higher-Q action:

      prefers-action-zero? q0 q1 = decide (q1 <= q0)
      best-q               q0 q1 = if (q1 <= q0) then q0 else q1   (the larger Q)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  max value, and the switch when the second candidate is larger. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rl-falsification`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- pref [a b] (function/app (function/const* 'rl-fal/prefers-action-zero? []) a b))
(defn- mval [a b] (function/app (function/const* 'rl-fal/best-q []) a b))

(def pref-spec
  {:name 'rl-fal/prefers-action-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['q0 nnrat] ['q1 nnrat]] (decide-at-most 'q1 'q0))})

(def mval-spec
  {:name 'rl-fal/best-q :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['q0 nnrat] ['q1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'q1 'q0))
                                      (decide-at-most 'q1 'q0) 'q0 'q1))})

(def definition-specs [pref-spec mval-spec])

(def prefers-higher-spec
  {:name 'rl-fal/prefers-higher :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def value-is-maximum-spec
  {:name 'rl-fal/value-is-maximum :universes []
   :type (equality nnrat (mval (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (mval (fraction 3 3) (fraction 1 1)))})

(def switches-spec
  {:name 'rl-fal/switches :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [prefers-higher-spec value-is-maximum-spec switches-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-rl-falsification
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
