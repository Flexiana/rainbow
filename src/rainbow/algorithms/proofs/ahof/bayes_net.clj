(ns rainbow.algorithms.proofs.ahof.bayes-net
  "AHoF D1 Bayesian Network Representation: the joint distribution factorizes as a\n  product of conditional-probability factors; the joint mass of two factors is their\n  product joint-factor a b = a * b. Proved native and axiom-free (worked masses by\n  cross-product equivalence).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayes-net`
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
(def one-half (make-rational 1 1))
(def one-quarter (make-rational 1 3))
(def one-eighth (make-rational 1 7))
(def one-sixteenth (make-rational 1 15))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'bayes-net/joint-factor []) a b))

(def op-spec
  {:name 'bayes-net/joint-factor :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]] (nnrat-multiply 'a 'b))})

(def high-spec
  {:name 'bayes-net/strong-factor :kind :definition :universes [] :type nnrat
   :value (op one-half one-quarter)})
(def low-spec
  {:name 'bayes-net/weak-factor :kind :definition :universes [] :type nnrat
   :value (op one-quarter one-quarter)})

(def definition-specs [op-spec high-spec low-spec])

(def op-unfold-spec
  {:name 'bayes-net/joint-factor-unfold :universes []
   :type (function/forall [['a nnrat] ['b nnrat]]
                          (equality nnrat (op 'a 'b) (nnrat-multiply 'a 'b)))
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (op 'a 'b)))})

(def high-is-eighth-spec
  {:name 'bayes-net/strong-factor-is-one-eighth :universes []
   :type (nnrat-equivalent (function/const* 'bayes-net/strong-factor []) one-eighth)
   :value (equivalent-cross (function/const* 'bayes-net/strong-factor []) one-eighth)})

(def low-is-sixteenth-spec
  {:name 'bayes-net/weak-factor-is-one-sixteenth :universes []
   :type (nnrat-equivalent (function/const* 'bayes-net/weak-factor []) one-sixteenth)
   :value (equivalent-cross (function/const* 'bayes-net/weak-factor []) one-sixteenth)})

(def combined-spec
  (let [a (:type high-is-eighth-spec) b (:type low-is-sixteenth-spec)]
    {:name 'bayes-net/combined :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'bayes-net/strong-factor-is-one-eighth [])
                          (function/const* 'bayes-net/weak-factor-is-one-sixteenth []))}))

(def theorem-specs [op-unfold-spec high-is-eighth-spec low-is-sixteenth-spec combined-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bayes-net
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
