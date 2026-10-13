(ns rainbow.algorithms.proofs.ahof.is-falsification
  "AHoF V27 Importance Sampling: estimate the probability of a rare failure event by
  sampling from a proposal distribution and reweighting by the importance weight, the
  ratio of the target density to the proposal density:

      importance-weight target proposal = target / proposal.

  The ratio reading holds only for a POSITIVE proposal density. nnrat/divide is
  totalised: a zero proposal is accepted and yields a junk value (its reciprocal maps the
  equivalent zeros 0/1 and 0/2 to 1 and 2), and that zero case lies outside the
  importance-weight claim. Proved: importance-weight unfolds to nnrat/divide for all
  inputs (by reflexivity, an unfolding and not a ratio claim), a sample drawn under
  proposal 1/4 for a target 1/2 carries weight 2, and a sample whose target and proposal
  agree (1/4, 1/4) carries weight 1. Weights are proved by cross-product equivalence.
  Proved native and axiom-free. Requires nnrat/divide, nnrat/equivalent (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.is-falsification`
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

(defn- importance-weight [target proposal]
  (function/app (function/const* 'is-weight/importance-weight []) target proposal))

(def importance-weight-spec
  {:name 'is-weight/importance-weight :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['target nnrat] ['proposal nnrat]]
                        (nnrat-divide 'target 'proposal))})

(def rare-event-weight-spec
  {:name 'is-weight/rare-event-weight :kind :definition :universes [] :type nnrat
   :value (importance-weight one-half one-quarter)})
(def matched-weight-spec
  {:name 'is-weight/matched-weight :kind :definition :universes [] :type nnrat
   :value (importance-weight one-quarter one-quarter)})

(def definition-specs [importance-weight-spec rare-event-weight-spec matched-weight-spec])

(def unfold-spec
  {:name 'is-weight/importance-weight-unfold :universes []
   :type (function/forall [['target nnrat] ['proposal nnrat]]
                          (equality nnrat (importance-weight 'target 'proposal)
                                    (nnrat-divide 'target 'proposal)))
   :value (function/lam [['target nnrat] ['proposal nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (importance-weight 'target 'proposal)))})

;; A rare-event sample (target 1/2, proposal 1/4) carries weight 2.
(def rare-event-weight-is-two-spec
  {:name 'is-weight/rare-event-weight-is-two :universes []
   :type (nnrat-equivalent (function/const* 'is-weight/rare-event-weight []) two)
   :value (equivalent-cross (function/const* 'is-weight/rare-event-weight []) two)})

;; A matched sample (target = proposal) carries weight 1.
(def matched-weight-is-one-spec
  {:name 'is-weight/matched-weight-is-one :universes []
   :type (nnrat-equivalent (function/const* 'is-weight/matched-weight []) one)
   :value (equivalent-cross (function/const* 'is-weight/matched-weight []) one)})

(def theorem-specs
  [unfold-spec rare-event-weight-is-two-spec matched-weight-is-one-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-is-falsification
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
