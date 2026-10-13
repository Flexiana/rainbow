(ns rainbow.algorithms.proofs.ahof.correlated-equilibrium
  "AHoF D78 Correlated Equilibrium: a distribution over joint action profiles from
  which no player has an incentive to deviate from the mediator's recommendation; the
  per-player adherence test compares a deviation payoff against the recommended one:

      follows-recommendation? recommended deviation = decide (deviation <= recommended).
  Proved native and axiom-free (decision, two positive instances, at-most certificate,
  negative instance). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.correlated-equilibrium`
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
(defn- pred [a b]
  (function/app (function/const* 'correlated/follows-recommendation? []) a b))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def pred-spec
  {:name 'correlated/follows-recommendation? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['recommended nnrat] ['deviation nnrat]] (decide-at-most 'deviation 'recommended))})

(def definition-specs [pred-spec])

(def adheres-to-recommendation-spec
  {:name 'correlated/adheres-to-recommendation :universes []
   :type (equality bool (pred (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 3 3) (fraction 1 1)))})

(def boundary-adheres-spec
  {:name 'correlated/boundary-adheres :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 1 1)))})

(def adherence-certificate-spec
  {:name 'correlated/adherence-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def profitable-deviation-breaks-spec
  {:name 'correlated/profitable-deviation-breaks :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 3 3)))})

(def theorem-specs [adheres-to-recommendation-spec boundary-adheres-spec adherence-certificate-spec profitable-deviation-breaks-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-correlated-equilibrium
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
