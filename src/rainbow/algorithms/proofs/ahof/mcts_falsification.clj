(ns rainbow.algorithms.proofs.ahof.mcts-falsification
  "AHoF V19 MCTS for Falsification: Monte Carlo tree search over the space of system
  behaviours to find a specification violation, selecting child nodes by their UCB
  score and keeping the higher-scoring child:

      prefers-child-zero? u0 u1 = decide (u1 <= u0)
      tree-value          u0 u1 = if (u1 <= u0) then u0 else u1   (the larger UCB)

  over exact rationals. Proved native and axiom-free: the selection decision, the
  tree value (max), and the switch when the second child scores higher. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mcts-falsification`
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
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- prefers-child-zero? [u0 u1]
  (function/app (function/const* 'mcts-fal/prefers-child-zero? []) u0 u1))
(defn- tree-value [u0 u1]
  (function/app (function/const* 'mcts-fal/tree-value []) u0 u1))

(def prefers-spec
  {:name 'mcts-fal/prefers-child-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]] (decide-at-most 'u1 'u0))})

(def tree-value-spec
  {:name 'mcts-fal/tree-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'u1 'u0))
                                      (decide-at-most 'u1 'u0) 'u0 'u1))})

(def definition-specs [prefers-spec tree-value-spec])

(def prefers-higher-ucb-spec
  {:name 'mcts-fal/prefers-higher-ucb :universes []
   :type (equality bool (prefers-child-zero? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-child-zero? (fraction 3 3) (fraction 1 1)))})

(def tree-value-is-maximum-spec
  {:name 'mcts-fal/tree-value-is-maximum :universes []
   :type (equality nnrat (tree-value (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (tree-value (fraction 3 3) (fraction 1 1)))})

(def switches-child-spec
  {:name 'mcts-fal/switches-child :universes []
   :type (equality bool (prefers-child-zero? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-child-zero? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [prefers-higher-ucb-spec tree-value-is-maximum-spec switches-child-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-mcts-falsification (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.mcts-falsification))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
