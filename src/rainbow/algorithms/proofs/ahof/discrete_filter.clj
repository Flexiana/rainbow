(ns rainbow.algorithms.proofs.ahof.discrete-filter
  "AHoF D66 Discrete State Filter (recursive Bayesian filtering over a finite state
  space): each step multiplies the prior belief in a state by the measurement
  likelihood to get the unnormalized posterior weight, then renormalizes:

      posterior-weight likelihood prior = likelihood * prior.

  A state with likelihood 1/2 and prior 1/4 gets weight 1/8; a less-likely state
  (likelihood 1/4, prior 1/4) gets the smaller weight 1/16, so the update concentrates
  belief on better-explained states. Weights are proved by cross-product equivalence.
  Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.discrete-filter`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def one-half (make-rational 1 1))       ; 1/2
(def one-quarter (make-rational 1 3))    ; 1/4
(def one-eighth (make-rational 1 7))     ; 1/8
(def one-sixteenth (make-rational 1 15)) ; 1/16

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- posterior-weight [likelihood prior]
  (function/app (function/const* 'discrete-filter/posterior-weight []) likelihood prior))

(def posterior-weight-spec
  {:name 'discrete-filter/posterior-weight :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (nnrat-multiply 'likelihood 'prior))})

(def high-state-spec
  {:name 'discrete-filter/high-state :kind :definition :universes [] :type nnrat
   :value (posterior-weight one-half one-quarter)})
(def low-state-spec
  {:name 'discrete-filter/low-state :kind :definition :universes [] :type nnrat
   :value (posterior-weight one-quarter one-quarter)})

(def definition-specs [posterior-weight-spec high-state-spec low-state-spec])

(def posterior-weight-unfold-spec
  {:name 'discrete-filter/posterior-weight-unfold :universes []
   :type (function/forall [['likelihood nnrat] ['prior nnrat]]
                          (equality nnrat (posterior-weight 'likelihood 'prior)
                                    (nnrat-multiply 'likelihood 'prior)))
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (posterior-weight 'likelihood 'prior)))})

;; The better-explained state gets weight 1/8.
(def high-weight-spec
  {:name 'discrete-filter/high-weight-is-one-eighth :universes []
   :type (nnrat-equivalent (function/const* 'discrete-filter/high-state []) one-eighth)
   :value (equivalent-cross (function/const* 'discrete-filter/high-state []) one-eighth)})

;; The less-likely state gets the smaller weight 1/16.
(def low-weight-spec
  {:name 'discrete-filter/low-weight-is-one-sixteenth :universes []
   :type (nnrat-equivalent (function/const* 'discrete-filter/low-state []) one-sixteenth)
   :value (equivalent-cross (function/const* 'discrete-filter/low-state []) one-sixteenth)})

(def discrete-filter-spec
  (let [hi (:type high-weight-spec) lo (:type low-weight-spec)]
    {:name 'discrete-filter/discrete-filter :universes []
     :type (proposition/conjunction hi lo)
     :value (function/app (function/const* 'proposition/conjoin []) hi lo
                          (function/const* 'discrete-filter/high-weight-is-one-eighth [])
                          (function/const* 'discrete-filter/low-weight-is-one-sixteenth []))}))

(def theorem-specs
  [posterior-weight-unfold-spec high-weight-spec low-weight-spec discrete-filter-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-discrete-filter
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
