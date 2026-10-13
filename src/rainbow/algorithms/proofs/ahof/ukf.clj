(ns rainbow.algorithms.proofs.ahof.ukf
  "AHoF D69 Unscented Kalman Filter: propagate a small set of deterministically chosen
  sigma points through the nonlinear model and recover the posterior mean as their
  weighted average. With two sigma points the recovered mean is the weighted sum:

      sigma-mean w0 s0 w1 s1 = w0 * s0 + w1 * s1.

  Equal weights on sigma points 1/2 and 3/4 give the mean 5/8; weighting only the
  first sigma point (weights 1, 0) returns it, 1/2. Values are proved by cross-product
  equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ukf`
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

(defn- sigma-mean [w0 s0 w1 s1]
  (function/app (function/const* 'ukf/sigma-mean []) w0 s0 w1 s1))

(def sigma-mean-spec
  {:name 'ukf/sigma-mean :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['s0 nnrat] ['w1 nnrat] ['s1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 's0)
                                   (nnrat-multiply 'w1 's1)))})

(def balanced-mean-spec
  {:name 'ukf/balanced-mean :kind :definition :universes [] :type nnrat
   :value (sigma-mean half half half three-quarters)})
(def first-point-only-spec
  {:name 'ukf/first-point-only :kind :definition :universes [] :type nnrat
   :value (sigma-mean nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [sigma-mean-spec balanced-mean-spec first-point-only-spec])

(def sigma-mean-unfold-spec
  {:name 'ukf/sigma-mean-unfold :universes []
   :type (function/forall [['w0 nnrat] ['s0 nnrat] ['w1 nnrat] ['s1 nnrat]]
                          (equality nnrat (sigma-mean 'w0 's0 'w1 's1)
                                    (nnrat-add (nnrat-multiply 'w0 's0)
                                               (nnrat-multiply 'w1 's1))))
   :value (function/lam [['w0 nnrat] ['s0 nnrat] ['w1 nnrat] ['s1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (sigma-mean 'w0 's0 'w1 's1)))})

(def balanced-is-five-eighths-spec
  {:name 'ukf/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'ukf/balanced-mean []) five-eighths)
   :value (equivalent-cross (function/const* 'ukf/balanced-mean []) five-eighths)})

(def first-point-is-half-spec
  {:name 'ukf/first-point-is-half :universes []
   :type (nnrat-equivalent (function/const* 'ukf/first-point-only []) half)
   :value (equivalent-cross (function/const* 'ukf/first-point-only []) half)})

(def ukf-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type first-point-is-half-spec)]
    {:name 'ukf/ukf :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'ukf/balanced-is-five-eighths [])
                          (function/const* 'ukf/first-point-is-half []))}))

(def theorem-specs
  [sigma-mean-unfold-spec balanced-is-five-eighths-spec first-point-is-half-spec
   ukf-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-ukf
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
