(ns rainbow.algorithms.proofs.ahof.pomcp
  "AHoF D75 Online POMDP (POMCP): Monte Carlo tree search in belief space, selecting
  actions at each node by their UCB score and keeping the higher-scoring action. With
  two actions the search prefers action 0 when its UCB is at least action 1's and the
  node value is the larger UCB:

      prefers-action-zero? u0 u1 = decide (u1 <= u0)
      node-value           u0 u1 = if (u1 <= u0) then u0 else u1   (the larger UCB)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  node value (max), and the switch when action 1 scores higher. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pomcp`
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
(defn- prefers-action-zero? [u0 u1]
  (function/app (function/const* 'pomcp/prefers-action-zero? []) u0 u1))
(defn- node-value [u0 u1]
  (function/app (function/const* 'pomcp/node-value []) u0 u1))

(def prefers-spec
  {:name 'pomcp/prefers-action-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]] (decide-at-most 'u1 'u0))})

(def node-value-spec
  {:name 'pomcp/node-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['u0 nnrat] ['u1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'u1 'u0))
                                      (decide-at-most 'u1 'u0) 'u0 'u1))})

(def definition-specs [prefers-spec node-value-spec])

(def prefers-higher-ucb-spec
  {:name 'pomcp/prefers-higher-ucb :universes []
   :type (equality bool (prefers-action-zero? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-action-zero? (fraction 3 3) (fraction 1 1)))})

(def node-value-is-maximum-spec
  {:name 'pomcp/node-value-is-maximum :universes []
   :type (equality nnrat (node-value (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (node-value (fraction 3 3) (fraction 1 1)))})

(def switches-action-spec
  {:name 'pomcp/switches-action :universes []
   :type (equality bool (prefers-action-zero? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-action-zero? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [prefers-higher-ucb-spec node-value-is-maximum-spec switches-action-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-pomcp (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.pomcp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
