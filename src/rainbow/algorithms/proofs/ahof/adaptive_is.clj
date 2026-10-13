(ns rainbow.algorithms.proofs.ahof.adaptive-is
  "AHoF V28 Adaptive Importance Sampling: iteratively refine the proposal and reweight
  samples by the ratio of the target density to the current proposal density:

      reweight target proposal = target / proposal.

  The ratio reading holds only for a POSITIVE proposal density. nnrat/divide is
  totalised: a zero proposal is accepted and yields a junk value (its reciprocal maps the
  equivalent zeros 0/1 and 0/2 to 1 and 2), and that zero case lies outside the
  reweighting claim. Proved native and axiom-free: reweight unfolds to nnrat/divide for
  all inputs (by reflexivity, an unfolding and not a ratio claim), and the worked
  weights 1/2 / 1/4 = 2 and 1/4 / 1/4 = 1 via cross-product equivalence. Adaptive
  refinement of the proposal is not modelled here.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.adaptive-is`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def one-half (make-rational 1 1))
(def one-quarter (make-rational 1 3))
(def two (make-rational 2 0))
(def one (make-rational 1 0))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-divide [l r] (function/app (function/const* 'nnrat/divide []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'adaptive-is/reweight []) a b))

(def op-spec
  {:name 'adaptive-is/reweight :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['target nnrat] ['proposal nnrat]] (nnrat-divide 'target 'proposal))})

(def unequal-spec
  {:name 'adaptive-is/unequal-weight :kind :definition :universes [] :type nnrat
   :value (op one-half one-quarter)})
(def equal-spec
  {:name 'adaptive-is/equal-weight :kind :definition :universes [] :type nnrat
   :value (op one-quarter one-quarter)})

(def definition-specs [op-spec unequal-spec equal-spec])

(def unfold-spec
  {:name 'adaptive-is/reweight-unfold :universes []
   :type (function/forall [['target nnrat] ['proposal nnrat]]
                          (equality nnrat (op 'target 'proposal) (nnrat-divide 'target 'proposal)))
   :value (function/lam [['target nnrat] ['proposal nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (op 'target 'proposal)))})

(def unequal-is-two-spec
  {:name 'adaptive-is/unequal-is-two :universes []
   :type (nnrat-equivalent (function/const* 'adaptive-is/unequal-weight []) two)
   :value (equivalent-cross (function/const* 'adaptive-is/unequal-weight []) two)})

(def equal-is-one-spec
  {:name 'adaptive-is/equal-is-one :universes []
   :type (nnrat-equivalent (function/const* 'adaptive-is/equal-weight []) one)
   :value (equivalent-cross (function/const* 'adaptive-is/equal-weight []) one)})

(def theorem-specs [unfold-spec unequal-is-two-spec equal-is-one-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-adaptive-is
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
