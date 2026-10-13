(ns rainbow.algorithms.proofs.ahof.stl-monitor
  "AHoF V63 Runtime STL Monitor: online monitoring of a Signal Temporal Logic
  specification. The monitor tracks the quantitative robustness margin of the signal
  and reports the spec as satisfied while that margin stays at or above a required
  safety margin:

      satisfied? robustness margin = decide (margin <= robustness).

  A robustness of 3/4 against a required margin 1/2 is satisfied; a margin exactly met
  is still satisfied; a robustness of 1/4 below the margin is a runtime violation.
  Proved native and axiom-free (decision, boundary, at-most certificate, violation).
  Requires audit/decide-nnrat-at-most, nnrat/at-most, nnrat/decide-at-most-true-sound.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.stl-monitor`
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
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- satisfied? [robustness margin]
  (function/app (function/const* 'stl-monitor/satisfied? []) robustness margin))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def satisfied-spec
  {:name 'stl-monitor/satisfied? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['robustness nnrat] ['margin nnrat]]
                        (decide-at-most 'margin 'robustness))})

(def definition-specs [satisfied-spec])

(def satisfied-above-margin-spec
  {:name 'stl-monitor/satisfied-above-margin :universes []
   :type (equality bool (satisfied? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfied? (fraction 3 3) (fraction 1 1)))})

(def satisfied-at-margin-spec
  {:name 'stl-monitor/satisfied-at-margin :universes []
   :type (equality bool (satisfied? (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfied? (fraction 1 1) (fraction 1 1)))})

(def robustness-certificate-spec
  {:name 'stl-monitor/robustness-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def violated-below-margin-spec
  {:name 'stl-monitor/violated-below-margin :universes []
   :type (equality bool (satisfied? (fraction 1 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfied? (fraction 1 3) (fraction 1 1)))})

(def theorem-specs
  [satisfied-above-margin-spec satisfied-at-margin-spec
   robustness-certificate-spec violated-below-margin-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-stl-monitor
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
