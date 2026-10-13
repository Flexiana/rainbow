(ns rainbow.algorithms.proofs.ahof.counterfactual-cf
  "AHoF V57 Counterfactual Explanation: explain a model decision by the smallest change
  to the input that flips the prediction to a desired class. What is defined here is only
  the BUDGET-FEASIBILITY part of that check: a candidate passes when its change cost
  (distance from the original input) is within the user's action budget:

      valid-counterfactual? change-cost budget = decide (change-cost <= budget).

  Passing this test does not make a candidate a valid counterfactual; validity also needs
  the prediction to change to the desired class, which is not modelled here (an unchanged
  input of cost 0 within budget 1 passes even for a constant classifier f(x)=0 with
  desired class 1). Proved native and axiom-free, as worked instances: cost 1/2 within
  budget 3/4 passes, cost 1/2 at budget 1/2 passes, the certificate 1/2 <= 3/4, and cost
  3/4 over budget 1/2 is rejected. Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.counterfactual-cf`
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
(defn- valid-counterfactual? [change-cost budget]
  (function/app (function/const* 'cf/valid-counterfactual? []) change-cost budget))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def valid-counterfactual-spec
  {:name 'cf/valid-counterfactual? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['change-cost nnrat] ['budget nnrat]]
                        (decide-at-most 'change-cost 'budget))})

(def definition-specs [valid-counterfactual-spec])

(def within-budget-valid-spec
  {:name 'cf/within-budget-valid :universes []
   :type (equality bool (valid-counterfactual? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (valid-counterfactual? (fraction 1 1) (fraction 3 3)))})

(def boundary-valid-spec
  {:name 'cf/boundary-valid :universes []
   :type (equality bool (valid-counterfactual? (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (valid-counterfactual? (fraction 1 1) (fraction 1 1)))})

(def proximity-certificate-spec
  {:name 'cf/proximity-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def over-budget-rejected-spec
  {:name 'cf/over-budget-rejected :universes []
   :type (equality bool (valid-counterfactual? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (valid-counterfactual? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [within-budget-valid-spec boundary-valid-spec proximity-certificate-spec
   over-budget-rejected-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-counterfactual-cf (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.counterfactual-cf))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
