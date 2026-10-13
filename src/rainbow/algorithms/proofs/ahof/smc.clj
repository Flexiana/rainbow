(ns rainbow.algorithms.proofs.ahof.smc
  "AHoF V30 Sequential Monte Carlo: propagate and resample a weighted particle set over
  time; the filtered estimate is the normalized weighted mean of the particles,
  estimate w0 x0 w1 x1 = w0*x0 + w1*x1. Balanced weights on particles 1/2 and 3/4 give
  5/8; weight on the first particle only gives 1/2. Proved native and axiom-free (by
  cross-product equivalence).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.smc`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- estimate [w0 x0 w1 x1] (function/app (function/const* 'smc/estimate []) w0 x0 w1 x1))

(def estimate-spec
  {:name 'smc/estimate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 'x0) (nnrat-multiply 'w1 'x1)))})

(def balanced-spec
  {:name 'smc/balanced :kind :definition :universes [] :type nnrat
   :value (estimate half half half three-quarters)})
(def single-spec
  {:name 'smc/single :kind :definition :universes [] :type nnrat
   :value (estimate nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [estimate-spec balanced-spec single-spec])

(def estimate-unfold-spec
  {:name 'smc/estimate-unfold :universes []
   :type (function/forall [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                          (equality nnrat (estimate 'w0 'x0 'w1 'x1)
                                    (nnrat-add (nnrat-multiply 'w0 'x0) (nnrat-multiply 'w1 'x1))))
   :value (function/lam [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (estimate 'w0 'x0 'w1 'x1)))})

(def balanced-is-five-eighths-spec
  {:name 'smc/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'smc/balanced []) five-eighths)
   :value (equivalent-cross (function/const* 'smc/balanced []) five-eighths)})

(def single-is-first-spec
  {:name 'smc/single-is-first :universes []
   :type (nnrat-equivalent (function/const* 'smc/single []) half)
   :value (equivalent-cross (function/const* 'smc/single []) half)})

(def combined-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type single-is-first-spec)]
    {:name 'smc/combined :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'smc/balanced-is-five-eighths [])
                          (function/const* 'smc/single-is-first []))}))

(def theorem-specs [estimate-unfold-spec balanced-is-five-eighths-spec single-is-first-spec combined-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-smc (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.smc))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
