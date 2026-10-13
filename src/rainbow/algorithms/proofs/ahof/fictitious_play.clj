(ns rainbow.algorithms.proofs.ahof.fictitious-play
  "AHoF D79 Fictitious Play: in a repeated game each player best-responds to the
  empirical frequency of the opponent's past actions. With two candidate actions the
  best response keeps the higher expected payoff and prefers action 0 when its payoff
  is at least action 1's:

      prefers-action-zero? p0 p1 = decide (p1 <= p0)
      best-response-value  p0 p1 = if (p1 <= p0) then p0 else p1   (the larger payoff)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  best-response (max) value, and the switch when action 1 pays more. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fictitious-play`
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
(defn- prefers-action-zero? [p0 p1]
  (function/app (function/const* 'fictitious/prefers-action-zero? []) p0 p1))
(defn- best-response-value [p0 p1]
  (function/app (function/const* 'fictitious/best-response-value []) p0 p1))

(def prefers-spec
  {:name 'fictitious/prefers-action-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['p0 nnrat] ['p1 nnrat]] (decide-at-most 'p1 'p0))})

(def best-response-spec
  {:name 'fictitious/best-response-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p0 nnrat] ['p1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'p1 'p0))
                                      (decide-at-most 'p1 'p0) 'p0 'p1))})

(def definition-specs [prefers-spec best-response-spec])

(def prefers-higher-payoff-spec
  {:name 'fictitious/prefers-higher-payoff :universes []
   :type (equality bool (prefers-action-zero? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-action-zero? (fraction 3 3) (fraction 1 1)))})

(def best-response-is-larger-spec
  {:name 'fictitious/best-response-is-larger :universes []
   :type (equality nnrat (best-response-value (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-response-value (fraction 3 3) (fraction 1 1)))})

(def switches-when-lower-spec
  {:name 'fictitious/switches-when-lower :universes []
   :type (equality bool (prefers-action-zero? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-action-zero? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [prefers-higher-payoff-spec best-response-is-larger-spec switches-when-lower-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-fictitious-play (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.fictitious-play))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
