(ns rainbow.algorithms.proofs.ahof.bayesian-model-estimation
  "AHoF D59 Bayesian Model Estimation: score candidate models by their posterior
  probability, which is proportional to the data likelihood under the model times the
  model prior:

      posterior-score likelihood prior = likelihood * prior.

  A model with likelihood 1/2 and prior 1/4 scores 1/8; a worse-fitting model
  (likelihood 1/4, prior 1/4) scores 1/16, so posterior mass concentrates on
  better-fitting models. Scores are proved by cross-product equivalence. Proved native
  and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayesian-model-estimation`
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

(defn- posterior-score [likelihood prior]
  (function/app (function/const* 'model-est/posterior-score []) likelihood prior))

(def posterior-score-spec
  {:name 'model-est/posterior-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (nnrat-multiply 'likelihood 'prior))})

(def good-model-spec
  {:name 'model-est/good-model :kind :definition :universes [] :type nnrat
   :value (posterior-score one-half one-quarter)})
(def poor-model-spec
  {:name 'model-est/poor-model :kind :definition :universes [] :type nnrat
   :value (posterior-score one-quarter one-quarter)})

(def definition-specs [posterior-score-spec good-model-spec poor-model-spec])

(def posterior-score-unfold-spec
  {:name 'model-est/posterior-score-unfold :universes []
   :type (function/forall [['likelihood nnrat] ['prior nnrat]]
                          (equality nnrat (posterior-score 'likelihood 'prior)
                                    (nnrat-multiply 'likelihood 'prior)))
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (posterior-score 'likelihood 'prior)))})

(def good-model-scores-one-eighth-spec
  {:name 'model-est/good-model-scores-one-eighth :universes []
   :type (nnrat-equivalent (function/const* 'model-est/good-model []) one-eighth)
   :value (equivalent-cross (function/const* 'model-est/good-model []) one-eighth)})

(def poor-model-scores-one-sixteenth-spec
  {:name 'model-est/poor-model-scores-one-sixteenth :universes []
   :type (nnrat-equivalent (function/const* 'model-est/poor-model []) one-sixteenth)
   :value (equivalent-cross (function/const* 'model-est/poor-model []) one-sixteenth)})

(def model-estimation-spec
  (let [a (:type good-model-scores-one-eighth-spec)
        b (:type poor-model-scores-one-sixteenth-spec)]
    {:name 'model-est/model-estimation :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'model-est/good-model-scores-one-eighth [])
                          (function/const* 'model-est/poor-model-scores-one-sixteenth []))}))

(def theorem-specs
  [posterior-score-unfold-spec good-model-scores-one-eighth-spec
   poor-model-scores-one-sixteenth-spec model-estimation-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-bayesian-model-estimation (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.bayesian-model-estimation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
