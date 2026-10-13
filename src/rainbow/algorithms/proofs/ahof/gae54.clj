(ns rainbow.algorithms.proofs.ahof.gae54
  "AHoF D54 Generalized Advantage Estimation: form a low-variance advantage estimate as
  an exponentially-weighted sum of one-step TD residuals; the recursive form combines
  the current residual with the discounted future advantage:

      gae-advantage delta lambda-gamma next-advantage
        = delta + lambda-gamma * next-advantage.

  A residual 1/4 with decay lambda-gamma 1/2 and future advantage 1/2 gives 1/2; the
  one-step (lambda-gamma 0) estimate is the residual 1/4. Values are proved by
  cross-product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gae54`
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

(defn- gae-advantage [delta lg next]
  (function/app (function/const* 'gae54/gae-advantage []) delta lg next))

(def gae-advantage-spec
  {:name 'gae54/gae-advantage :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['delta nnrat] ['lg nnrat] ['next nnrat]]
                        (nnrat-add 'delta (nnrat-multiply 'lg 'next)))})

(def recursive-estimate-spec
  {:name 'gae54/recursive-estimate :kind :definition :universes [] :type nnrat
   :value (gae-advantage one-quarter one-half one-half)})
(def one-step-estimate-spec
  {:name 'gae54/one-step-estimate :kind :definition :universes [] :type nnrat
   :value (gae-advantage one-quarter nnrat-zero one-half)})

(def definition-specs [gae-advantage-spec recursive-estimate-spec one-step-estimate-spec])

(def gae-advantage-unfold-spec
  {:name 'gae54/gae-advantage-unfold :universes []
   :type (function/forall [['delta nnrat] ['lg nnrat] ['next nnrat]]
                          (equality nnrat (gae-advantage 'delta 'lg 'next)
                                    (nnrat-add 'delta (nnrat-multiply 'lg 'next))))
   :value (function/lam [['delta nnrat] ['lg nnrat] ['next nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (gae-advantage 'delta 'lg 'next)))})

(def recursive-is-half-spec
  {:name 'gae54/recursive-is-half :universes []
   :type (nnrat-equivalent (function/const* 'gae54/recursive-estimate []) one-half)
   :value (equivalent-cross (function/const* 'gae54/recursive-estimate []) one-half)})

(def one-step-is-residual-spec
  {:name 'gae54/one-step-is-residual :universes []
   :type (nnrat-equivalent (function/const* 'gae54/one-step-estimate []) one-quarter)
   :value (equivalent-cross (function/const* 'gae54/one-step-estimate []) one-quarter)})

(def gae-spec
  (let [a (:type recursive-is-half-spec) b (:type one-step-is-residual-spec)]
    {:name 'gae54/gae :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'gae54/recursive-is-half [])
                          (function/const* 'gae54/one-step-is-residual []))}))

(def theorem-specs
  [gae-advantage-unfold-spec recursive-is-half-spec one-step-is-residual-spec gae-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-gae54
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
