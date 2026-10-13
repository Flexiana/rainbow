(ns rainbow.algorithms.proofs.ahof.shubert
  "AHoF O11 Shubert-Piyavskii: build a piecewise-linear (sawtooth) lower bound of a Lipschitz
  objective and sample where the lower bound is smallest; between two candidate lower-
  bound values it keeps the smaller value:

      prefers-lower? a b = decide ('a 'b)
      sample-value a b = if ('a 'b) then 'a else 'b

  over exact rationals. Proved native and axiom-free: the preference decision, the
  selected value, and the switch. Requires audit/decide-nnrat-at-most, logic/if-data
  (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.shubert`
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
(defn- pref [a b] (function/app (function/const* 'shubert/prefers-lower? []) a b))
(defn- sval [a b] (function/app (function/const* 'shubert/sample-value []) a b))

(def pref-spec
  {:name 'shubert/prefers-lower? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['a nnrat] ['b nnrat]] (decide-at-most 'a 'b))})

(def sval-spec
  {:name 'shubert/sample-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'a 'b)) (decide-at-most 'a 'b) 'a 'b))})

(def definition-specs [pref-spec sval-spec])

(def prefers-example-spec
  {:name 'shubert/prefers-example :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def selected-value-spec
  {:name 'shubert/selected-value :universes []
   :type (equality nnrat (sval (fraction 1 1) (fraction 3 3)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (sval (fraction 1 1) (fraction 3 3)))})

(def switches-spec
  {:name 'shubert/switches :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [prefers-example-spec selected-value-spec switches-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-shubert
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
