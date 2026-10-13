(ns rainbow.algorithms.proofs.ahof.mc-mean
  "AHoF O69 Uncertainty Propagation (Monte Carlo): propagate input uncertainty by
  sampling and averaging the outputs. The two-sample Monte Carlo mean estimator
  weights each sample equally:

      estimate s1 s2 = 1/2 * s1 + 1/2 * s2.

  Averaging samples 1/2 and 3/4 gives the mean 5/8; averaging 1/4 and 3/4 gives 1/2.
  Values are proved by cross-product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mc-mean`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def half (make-rational 1 1))            ; 1/2
(def one-quarter (make-rational 1 3))     ; 1/4
(def three-quarters (make-rational 3 3))  ; 3/4
(def five-eighths (make-rational 5 7))    ; 5/8

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

(defn- estimate [s1 s2]
  (function/app (function/const* 'mc-mean/estimate []) s1 s2))

(def estimate-spec
  {:name 'mc-mean/estimate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['s1 nnrat] ['s2 nnrat]]
                        (nnrat-add (nnrat-multiply half 's1)
                                   (nnrat-multiply half 's2)))})

(def sample-mean-spec
  {:name 'mc-mean/sample-mean :kind :definition :universes [] :type nnrat
   :value (estimate half three-quarters)})
(def balanced-mean-spec
  {:name 'mc-mean/balanced-mean :kind :definition :universes [] :type nnrat
   :value (estimate one-quarter three-quarters)})

(def definition-specs [estimate-spec sample-mean-spec balanced-mean-spec])

(def estimate-unfold-spec
  {:name 'mc-mean/estimate-unfold :universes []
   :type (function/forall [['s1 nnrat] ['s2 nnrat]]
                          (equality nnrat (estimate 's1 's2)
                                    (nnrat-add (nnrat-multiply half 's1)
                                               (nnrat-multiply half 's2))))
   :value (function/lam [['s1 nnrat] ['s2 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (estimate 's1 's2)))})

;; The mean of 1/2 and 3/4 is 5/8.
(def sample-mean-is-five-eighths-spec
  {:name 'mc-mean/sample-mean-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'mc-mean/sample-mean []) five-eighths)
   :value (equivalent-cross (function/const* 'mc-mean/sample-mean []) five-eighths)})

;; The mean of 1/4 and 3/4 is 1/2.
(def balanced-mean-is-half-spec
  {:name 'mc-mean/balanced-mean-is-half :universes []
   :type (nnrat-equivalent (function/const* 'mc-mean/balanced-mean []) half)
   :value (equivalent-cross (function/const* 'mc-mean/balanced-mean []) half)})

(def mc-mean-spec
  (let [a (:type sample-mean-is-five-eighths-spec)
        b (:type balanced-mean-is-half-spec)]
    {:name 'mc-mean/mc-mean :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'mc-mean/sample-mean-is-five-eighths [])
                          (function/const* 'mc-mean/balanced-mean-is-half []))}))

(def theorem-specs
  [estimate-unfold-spec sample-mean-is-five-eighths-spec balanced-mean-is-half-spec
   mc-mean-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-mc-mean (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.mc-mean))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
