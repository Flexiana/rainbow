(ns rainbow.algorithms.proofs.ahof.genetic-programming
  "AHoF O70 Genetic Programming: evolve programs represented as expression trees under
  fitness selection; between two candidate programs it keeps the fitter (higher-
  fitness) one:

      prefers-fitter? f0 f1 = decide (f1 <= f0)
      best-fitness    f0 f1 = if (f1 <= f0) then f0 else f1   (the higher fitness)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  max value, and the switch when the second candidate is larger. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.genetic-programming`
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
(defn- pref [a b] (function/app (function/const* 'gp-tree/prefers-fitter? []) a b))
(defn- mval [a b] (function/app (function/const* 'gp-tree/best-fitness []) a b))

(def pref-spec
  {:name 'gp-tree/prefers-fitter? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['f0 nnrat] ['f1 nnrat]] (decide-at-most 'f1 'f0))})

(def mval-spec
  {:name 'gp-tree/best-fitness :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['f0 nnrat] ['f1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'f1 'f0))
                                      (decide-at-most 'f1 'f0) 'f0 'f1))})

(def definition-specs [pref-spec mval-spec])

(def prefers-higher-spec
  {:name 'gp-tree/prefers-higher :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def value-is-maximum-spec
  {:name 'gp-tree/value-is-maximum :universes []
   :type (equality nnrat (mval (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (mval (fraction 3 3) (fraction 1 1)))})

(def switches-spec
  {:name 'gp-tree/switches :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [prefers-higher-spec value-is-maximum-spec switches-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-genetic-programming (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.genetic-programming))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
