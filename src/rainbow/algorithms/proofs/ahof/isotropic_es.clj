(ns rainbow.algorithms.proofs.ahof.isotropic-es
  "AHoF D44 Isotropic Evolutionary Strategies: perturb with isotropic Gaussian noise and keep
  the fitter offspring; between two fitnesses it keeps the larger value:

      prefers-fitter? a b = decide ('b 'a)
      selected-fitness a b = if ('b 'a) then 'a else 'b

  over exact rationals. Proved native and axiom-free: the preference decision, the
  selected value, and the switch. Requires audit/decide-nnrat-at-most, logic/if-data
  (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.isotropic-es`
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
(defn- pref [a b] (function/app (function/const* 'iso-es/prefers-fitter? []) a b))
(defn- sval [a b] (function/app (function/const* 'iso-es/selected-fitness []) a b))

(def pref-spec
  {:name 'iso-es/prefers-fitter? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['a nnrat] ['b nnrat]] (decide-at-most 'b 'a))})

(def sval-spec
  {:name 'iso-es/selected-fitness :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'b 'a)) (decide-at-most 'b 'a) 'a 'b))})

(def definition-specs [pref-spec sval-spec])

(def prefers-example-spec
  {:name 'iso-es/prefers-example :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def selected-value-spec
  {:name 'iso-es/selected-value :universes []
   :type (equality nnrat (sval (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (sval (fraction 3 3) (fraction 1 1)))})

(def switches-spec
  {:name 'iso-es/switches :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [prefers-example-spec selected-value-spec switches-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-isotropic-es
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
