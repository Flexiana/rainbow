(ns rainbow.algorithms.proofs.ahof.actor-critic
  "AHoF D53 Actor-Critic: the critic bootstraps a temporal-difference target from the
  immediate reward plus the discounted value of the next state, and the actor is
  updated toward it. The bootstrap target is:

      td-target reward discount next-value = reward + discount * next-value.

  A reward 1/4 with discount 1/2 and next-value 1/2 gives the target 1/4 + 1/4 = 1/2;
  an undiscounted reward-only target (discount 0) is the reward 1/4. Values are proved
  by cross-product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.actor-critic`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def one-quarter (make-rational 1 3))
(def one-half (make-rational 1 1))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- td-target [reward discount next-value]
  (function/app (function/const* 'actor-critic/td-target []) reward discount next-value))

(def td-target-spec
  {:name 'actor-critic/td-target :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['reward nnrat] ['discount nnrat] ['next-value nnrat]]
                        (nnrat-add 'reward (nnrat-multiply 'discount 'next-value)))})

(def bootstrap-target-spec
  {:name 'actor-critic/bootstrap-target :kind :definition :universes [] :type nnrat
   :value (td-target one-quarter one-half one-half)})
(def reward-only-target-spec
  {:name 'actor-critic/reward-only-target :kind :definition :universes [] :type nnrat
   :value (td-target one-quarter nnrat-zero one-half)})

(def definition-specs [td-target-spec bootstrap-target-spec reward-only-target-spec])

(def td-target-unfold-spec
  {:name 'actor-critic/td-target-unfold :universes []
   :type (function/forall [['reward nnrat] ['discount nnrat] ['next-value nnrat]]
                          (equality nnrat (td-target 'reward 'discount 'next-value)
                                    (nnrat-add 'reward (nnrat-multiply 'discount 'next-value))))
   :value (function/lam [['reward nnrat] ['discount nnrat] ['next-value nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (td-target 'reward 'discount 'next-value)))})

(def bootstrap-is-half-spec
  {:name 'actor-critic/bootstrap-is-half :universes []
   :type (nnrat-equivalent (function/const* 'actor-critic/bootstrap-target []) one-half)
   :value (equivalent-cross (function/const* 'actor-critic/bootstrap-target []) one-half)})

(def reward-only-is-reward-spec
  {:name 'actor-critic/reward-only-is-reward :universes []
   :type (nnrat-equivalent (function/const* 'actor-critic/reward-only-target []) one-quarter)
   :value (equivalent-cross (function/const* 'actor-critic/reward-only-target []) one-quarter)})

(def actor-critic-spec
  (let [a (:type bootstrap-is-half-spec) b (:type reward-only-is-reward-spec)]
    {:name 'actor-critic/actor-critic :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'actor-critic/bootstrap-is-half [])
                          (function/const* 'actor-critic/reward-only-is-reward []))}))

(def theorem-specs
  [td-target-unfold-spec bootstrap-is-half-spec reward-only-is-reward-spec
   actor-critic-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-actor-critic
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
