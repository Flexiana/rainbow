(ns rainbow.algorithms.proofs.ahof.tree-search-fal
  "AHoF V17 Tree Search for Falsification: best-first search over behaviours toward a
  violation, expanding the node with the lowest cost-to-violation; it keeps the smaller value:

      prefers-lower-cost? a b = decide ('a 'b)
      frontier-value a b = if ('a 'b) then 'a else 'b

  over exact rationals. Proved native and axiom-free: the preference decision, the
  selected value, and the switch. Requires audit/decide-nnrat-at-most, logic/if-data
  (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.tree-search-fal`
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
(defn- pref [a b] (function/app (function/const* 'tree-fal/prefers-lower-cost? []) a b))
(defn- sval [a b] (function/app (function/const* 'tree-fal/frontier-value []) a b))

(def pref-spec
  {:name 'tree-fal/prefers-lower-cost? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['a nnrat] ['b nnrat]] (decide-at-most 'a 'b))})

(def sval-spec
  {:name 'tree-fal/frontier-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'a 'b)) (decide-at-most 'a 'b) 'a 'b))})

(def definition-specs [pref-spec sval-spec])

(def prefers-example-spec
  {:name 'tree-fal/prefers-example :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def selected-value-spec
  {:name 'tree-fal/selected-value :universes []
   :type (equality nnrat (sval (fraction 1 1) (fraction 3 3)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (sval (fraction 1 1) (fraction 3 3)))})

(def switches-spec
  {:name 'tree-fal/switches :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [prefers-example-spec selected-value-spec switches-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-tree-search-fal (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.tree-search-fal))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
