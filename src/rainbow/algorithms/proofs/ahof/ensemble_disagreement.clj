(ns rainbow.algorithms.proofs.ahof.ensemble-disagreement
  "AHoF V61 Ensemble Disagreement: quantify predictive uncertainty by the spread of an
  ensemble's predictions and flag an input as uncertain when the disagreement reaches
  a threshold:

      flag-uncertain? disagreement threshold = decide (threshold <= disagreement).

  A disagreement of 3/4 against threshold 1/2 is flagged uncertain; a disagreement of
  1/4 is confident (not flagged). Proved native and axiom-free (decision, flagged and
  confident instances, at-most certificate). Requires audit/decide-nnrat-at-most,
  nnrat/at-most, nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ensemble-disagreement`
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
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- flag-uncertain? [disagreement threshold]
  (function/app (function/const* 'ensemble/flag-uncertain? []) disagreement threshold))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def flag-spec
  {:name 'ensemble/flag-uncertain? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['disagreement nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'disagreement))})

(def definition-specs [flag-spec])

(def high-disagreement-flagged-spec
  {:name 'ensemble/high-disagreement-flagged :universes []
   :type (equality bool (flag-uncertain? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flag-uncertain? (fraction 3 3) (fraction 1 1)))})

(def disagreement-certificate-spec
  {:name 'ensemble/disagreement-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def low-disagreement-confident-spec
  {:name 'ensemble/low-disagreement-confident :universes []
   :type (equality bool (flag-uncertain? (fraction 1 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flag-uncertain? (fraction 1 3) (fraction 1 1)))})

(def theorem-specs
  [high-disagreement-flagged-spec disagreement-certificate-spec
   low-disagreement-confident-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-ensemble-disagreement (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.ensemble-disagreement))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
