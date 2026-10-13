(ns rainbow.algorithms.proofs.ahof.finite-state-controller
  "AHoF D76 Finite State Controller: a POMDP policy as a finite-state machine; at a controller
  node it selects the higher-value action; it keeps the larger value:

      prefers-action-zero? a b = decide ('b 'a)
      node-value a b = if ('b 'a) then 'a else 'b

  over exact rationals. Proved native and axiom-free: the preference decision, the
  selected value, and the switch. Requires audit/decide-nnrat-at-most, logic/if-data
  (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.finite-state-controller`
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
(defn- pref [a b] (function/app (function/const* 'fsc/prefers-action-zero? []) a b))
(defn- sval [a b] (function/app (function/const* 'fsc/node-value []) a b))

(def pref-spec
  {:name 'fsc/prefers-action-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['a nnrat] ['b nnrat]] (decide-at-most 'b 'a))})

(def sval-spec
  {:name 'fsc/node-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'b 'a)) (decide-at-most 'b 'a) 'a 'b))})

(def definition-specs [pref-spec sval-spec])

(def prefers-example-spec
  {:name 'fsc/prefers-example :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def selected-value-spec
  {:name 'fsc/selected-value :universes []
   :type (equality nnrat (sval (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (sval (fraction 3 3) (fraction 1 1)))})

(def switches-spec
  {:name 'fsc/switches :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [prefers-example-spec selected-value-spec switches-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-finite-state-controller (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.finite-state-controller))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
