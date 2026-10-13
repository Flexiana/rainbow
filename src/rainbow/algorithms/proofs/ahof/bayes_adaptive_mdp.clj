(ns rainbow.algorithms.proofs.ahof.bayes-adaptive-mdp
  "AHoF D60 Bayes-Adaptive MDP: plan in the belief-MDP over unknown model parameters,
  where the value of an action is the posterior-belief-weighted average of its value
  under each candidate model:

      expected-value b0 v0 b1 v1 = b0 * v0 + b1 * v1

  (belief weights b0, b1 summing to one). With equal belief 1/2, 1/2 over model values
  1/2, 3/4 the expected value is 5/8; with belief concentrated on the first model
  (weights 1, 0) it is that model's value 1/2. Values are proved by cross-product
  equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayes-adaptive-mdp`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def half (make-rational 1 1))
(def three-quarters (make-rational 3 3))
(def five-eighths (make-rational 5 7))

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

(defn- expected-value [b0 v0 b1 v1]
  (function/app (function/const* 'bamdp/expected-value []) b0 v0 b1 v1))

(def expected-value-spec
  {:name 'bamdp/expected-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['v0 nnrat] ['b1 nnrat] ['v1 nnrat]]
                        (nnrat-add (nnrat-multiply 'b0 'v0)
                                   (nnrat-multiply 'b1 'v1)))})

(def balanced-belief-spec
  {:name 'bamdp/balanced-belief :kind :definition :universes [] :type nnrat
   :value (expected-value half half half three-quarters)})
(def concentrated-belief-spec
  {:name 'bamdp/concentrated-belief :kind :definition :universes [] :type nnrat
   :value (expected-value nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [expected-value-spec balanced-belief-spec concentrated-belief-spec])

(def expected-value-unfold-spec
  {:name 'bamdp/expected-value-unfold :universes []
   :type (function/forall [['b0 nnrat] ['v0 nnrat] ['b1 nnrat] ['v1 nnrat]]
                          (equality nnrat (expected-value 'b0 'v0 'b1 'v1)
                                    (nnrat-add (nnrat-multiply 'b0 'v0)
                                               (nnrat-multiply 'b1 'v1))))
   :value (function/lam [['b0 nnrat] ['v0 nnrat] ['b1 nnrat] ['v1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (expected-value 'b0 'v0 'b1 'v1)))})

(def balanced-is-five-eighths-spec
  {:name 'bamdp/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'bamdp/balanced-belief []) five-eighths)
   :value (equivalent-cross (function/const* 'bamdp/balanced-belief []) five-eighths)})

(def concentrated-is-model-value-spec
  {:name 'bamdp/concentrated-is-model-value :universes []
   :type (nnrat-equivalent (function/const* 'bamdp/concentrated-belief []) half)
   :value (equivalent-cross (function/const* 'bamdp/concentrated-belief []) half)})

(def bamdp-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type concentrated-is-model-value-spec)]
    {:name 'bamdp/bayes-adaptive :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'bamdp/balanced-is-five-eighths [])
                          (function/const* 'bamdp/concentrated-is-model-value []))}))

(def theorem-specs
  [expected-value-unfold-spec balanced-is-five-eighths-spec
   concentrated-is-model-value-spec bamdp-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bayes-adaptive-mdp
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
