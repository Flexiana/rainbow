(ns rainbow.algorithms.proofs.ahof.bayesian-param
  "AHoF V2 Bayesian Parameter Learning: infer model parameters by their posterior, which
  is proportional to the data likelihood under the parameter times the parameter prior:

      posterior-score likelihood prior = likelihood * prior.

  A parameter with likelihood 1/2 and prior 1/4 scores 1/8; a worse-fitting parameter
  (likelihood 1/4, prior 1/4) scores 1/16, concentrating posterior mass on
  better-fitting parameters. Scores are proved by cross-product equivalence. Proved
  native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayesian-param`
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

(defn- posterior-score [likelihood prior]
  (function/app (function/const* 'bayes-param/posterior-score []) likelihood prior))

(def posterior-score-spec
  {:name 'bayes-param/posterior-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (nnrat-multiply 'likelihood 'prior))})

(def good-param-spec
  {:name 'bayes-param/good-param :kind :definition :universes [] :type nnrat
   :value (posterior-score one-half one-quarter)})
(def poor-param-spec
  {:name 'bayes-param/poor-param :kind :definition :universes [] :type nnrat
   :value (posterior-score one-quarter one-quarter)})

(def definition-specs [posterior-score-spec good-param-spec poor-param-spec])

(def posterior-score-unfold-spec
  {:name 'bayes-param/posterior-score-unfold :universes []
   :type (function/forall [['likelihood nnrat] ['prior nnrat]]
                          (equality nnrat (posterior-score 'likelihood 'prior)
                                    (nnrat-multiply 'likelihood 'prior)))
   :value (function/lam [['likelihood nnrat] ['prior nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (posterior-score 'likelihood 'prior)))})

(def good-param-scores-one-eighth-spec
  {:name 'bayes-param/good-param-scores-one-eighth :universes []
   :type (nnrat-equivalent (function/const* 'bayes-param/good-param []) one-eighth)
   :value (equivalent-cross (function/const* 'bayes-param/good-param []) one-eighth)})

(def poor-param-scores-one-sixteenth-spec
  {:name 'bayes-param/poor-param-scores-one-sixteenth :universes []
   :type (nnrat-equivalent (function/const* 'bayes-param/poor-param []) one-sixteenth)
   :value (equivalent-cross (function/const* 'bayes-param/poor-param []) one-sixteenth)})

(def bayesian-param-spec
  (let [a (:type good-param-scores-one-eighth-spec) b (:type poor-param-scores-one-sixteenth-spec)]
    {:name 'bayes-param/bayesian-param :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'bayes-param/good-param-scores-one-eighth [])
                          (function/const* 'bayes-param/poor-param-scores-one-sixteenth []))}))

(def theorem-specs
  [posterior-score-unfold-spec good-param-scores-one-eighth-spec
   poor-param-scores-one-sixteenth-spec bayesian-param-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bayesian-param
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
