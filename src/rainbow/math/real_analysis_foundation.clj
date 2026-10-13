(ns rainbow.math.real-analysis-foundation
  "FIRST brick of the real-analysis layer -- the gating foundation for frontier OR
  (convergence rates, GP regret, MDP contraction, LP duality all live over the reals).

  This module lays the sequence-order infrastructure that the monotone convergence
  theorem and Cauchy-real construction build on, using rational-valued sequences
  (nat -> nnrat) and the existing nnrat order.  It proves the pieces reachable with
  order-REFLEXIVITY alone:

    analysis/sequence            : nat -> nnrat
    analysis/nondecreasing s     : forall n, s n <= s (succ n)
    analysis/bounded-above s B    : forall n, s n <= B
    analysis/constant c           : the constant sequence
    analysis/constant-nondecreasing    : every constant sequence is nondecreasing
    analysis/constant-bounded-by-self  : a constant sequence is bounded by its value

  ROADMAP (the remaining real-analysis bedrock, in dependency order -- each needs the
  next; see rainbow-real-analysis-roadmap memory):
    nat multiplicative at-most cancellation -> nnrat closure<->base order equivalence
    -> nnrat additive at-most cancellation -> signed order transitivity + add-monotone
    -> the epsilon-N convergence predicate + squeeze theorem
    -> monotone convergence / Cauchy completeness -> limits, continuity, derivatives.

  Native and axiom-free; self-contained on d63 (uses only nnrat/at-most-reflexive)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def successor (function/const* 'data/succ []))

(defn- succ [v] (function/app successor v))
(defn- seq-type [] (function/arrow nat nnrat))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- at-most-reflexive [v]
  (function/app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- apply-seq [s n] (function/app s n))

;; nondecreasing predicate: forall n, s n <= s (succ n)
(def nondecreasing-spec
  {:name 'analysis/nondecreasing :kind :definition :universes []
   :type (function/arrow (seq-type) 'Prop)
   :value (function/lam [['s (seq-type)]]
                        (function/forall [['n nat]]
                                         (at-most (apply-seq 's 'n) (apply-seq 's (succ 'n)))))})

;; bounded-above predicate: forall n, s n <= B
(def bounded-above-spec
  {:name 'analysis/bounded-above :kind :definition :universes []
   :type (function/arrow (seq-type) nnrat 'Prop)
   :value (function/lam [['s (seq-type)] ['B nnrat]]
                        (function/forall [['n nat]] (at-most (apply-seq 's 'n) 'B)))})

;; the constant sequence
(def constant-spec
  {:name 'analysis/constant :kind :definition :universes []
   :type (function/arrow nnrat (seq-type))
   :value (function/lam [['c nnrat]] (function/lam [['n nat]] 'c))})

;; every constant sequence is nondecreasing (c <= c)
(def constant-nondecreasing-spec
  {:name 'analysis/constant-nondecreasing :universes []
   :type (function/forall [['c nnrat]]
                          (function/app (function/const* 'analysis/nondecreasing [])
                                        (function/app (function/const* 'analysis/constant []) 'c)))
   :value (function/lam [['c nnrat]]
                        (function/lam [['n nat]] (at-most-reflexive 'c)))})

;; a constant sequence is bounded above by its own value
(def constant-bounded-by-self-spec
  {:name 'analysis/constant-bounded-by-self :universes []
   :type (function/forall [['c nnrat]]
                          (function/app (function/const* 'analysis/bounded-above [])
                                        (function/app (function/const* 'analysis/constant []) 'c) 'c))
   :value (function/lam [['c nnrat]]
                        (function/lam [['n nat]] (at-most-reflexive 'c)))})

(def definition-specs [nondecreasing-spec bounded-above-spec constant-spec])
(def theorem-specs [constant-nondecreasing-spec constant-bounded-by-self-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :real-analysis-foundation
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
