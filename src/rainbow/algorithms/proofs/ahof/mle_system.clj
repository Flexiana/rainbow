(ns rainbow.algorithms.proofs.ahof.mle-system
  "AHoF V1 MLE for System Models: fit a system model by maximum likelihood, keeping the
  model with the larger data likelihood:

      prefers-model-zero? l0 l1 = decide (l1 <= l0)
      best-likelihood     l0 l1 = if (l1 <= l0) then l0 else l1

  over exact rationals. Proved native and axiom-free: preference decision, max value,
  switch. Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mle-system`
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
(defn- pref [a b] (function/app (function/const* 'mle/prefers-model-zero? []) a b))
(defn- mval [a b] (function/app (function/const* 'mle/best-likelihood []) a b))

(def pref-spec
  {:name 'mle/prefers-model-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['l0 nnrat] ['l1 nnrat]] (decide-at-most 'l1 'l0))})

(def mval-spec
  {:name 'mle/best-likelihood :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['l0 nnrat] ['l1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'l1 'l0))
                                      (decide-at-most 'l1 'l0) 'l0 'l1))})

(def definition-specs [pref-spec mval-spec])

(def prefers-higher-spec
  {:name 'mle/prefers-higher :universes []
   :type (equality bool (pref (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 3 3) (fraction 1 1)))})

(def value-is-maximum-spec
  {:name 'mle/value-is-maximum :universes []
   :type (equality nnrat (mval (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (mval (fraction 3 3) (fraction 1 1)))})

(def switches-spec
  {:name 'mle/switches :universes []
   :type (equality bool (pref (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pref (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [prefers-higher-spec value-is-maximum-spec switches-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-mle-system
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
