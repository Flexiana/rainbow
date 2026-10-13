(ns rainbow.algorithms.proofs.ahof.ucb
  "AHoF O64 Upper Confidence Bound acquisition (Bayesian optimization / bandits):
  select the next query by optimistically combining the surrogate's predicted
  mean with an exploration bonus proportional to the predictive uncertainty:

      ucb mean weight uncertainty = mean + weight * uncertainty

  over exact nonnegative rationals. The predictive mean and uncertainty come from
  the surrogate (a Gaussian process, whose sigma involves a square root, is an
  executable / not-exact-rational concern) and the exploration weight is a
  supplied rational; what is proved here is the deterministic optimistic
  combination and its optimism guarantee: the acquisition is at least the
  predicted mean (ucb >= mean), so UCB never underexplores relative to pure
  exploitation. Worked instances reduce by reflexivity on the exact rational
  arithmetic.

  Requires nnrat/add, nnrat/multiply, nnrat/at-most, and the decidable nnrat
  order (all in the D63 checkpoint)."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-upper :as add-upper]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- ucb [mean weight uncertainty]
  (function/app (function/const* 'ucb/acquisition []) mean weight uncertainty))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; ucb mean weight uncertainty = mean + weight * uncertainty
(def acquisition-spec
  {:name 'ucb/acquisition :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['mean nnrat] ['weight nnrat] ['uncertainty nnrat]]
                        (nnrat-add 'mean
                                   (nnrat-multiply 'weight 'uncertainty)))})

(def definition-specs [acquisition-spec])

;; Theorems -----------------------------------------------------------------

(def acquisition-unfold-spec
  {:name 'ucb/acquisition-unfold :universes []
   :type (function/forall
          [['mean nnrat] ['weight nnrat] ['uncertainty nnrat]]
          (equality nnrat
                    (ucb 'mean 'weight 'uncertainty)
                    (nnrat-add 'mean (nnrat-multiply 'weight 'uncertainty))))
   :value (function/lam [['mean nnrat] ['weight nnrat] ['uncertainty nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (ucb 'mean 'weight 'uncertainty)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked acquisition: mean 5, weight 1, uncertainty 2 -> 5 + 1*2 = 7.
(def acquisition-example-spec
  {:name 'ucb/acquisition-example :universes []
   :type (equality nnrat (ucb (whole 5) (whole 1) (whole 2)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ucb (whole 5) (whole 1) (whole 2)))})

;; Optimism: the acquisition is at least the predicted mean (5 <= 7), so UCB
;; never explores less than pure exploitation.
(def optimism-spec
  {:name 'ucb/at-least-mean :universes []
   :type (nnrat-at-most (whole 5) (ucb (whole 5) (whole 1) (whole 2)))
   :value (at-most-proof (whole 5) (ucb (whole 5) (whole 1) (whole 2)))})

(def optimism-universal-spec
  "The UNIVERSAL optimism guarantee: for EVERY mean, weight, and
  uncertainty, the acquisition score is at least the mean -- the
  exploration bonus weight*uncertainty is nonnegative, so UCB never
  underexplores relative to the pure mean. Upgrades the worked instance
  above to an all-inputs guarantee: mean <= mean + 0 <= mean + bonus,
  transporting add-zero-right across the monotone step."
  {:name 'ucb/at-least-mean-universal :universes []
   :type (function/forall
          [['mean nnrat] ['weight nnrat] ['uncertainty nnrat]]
          (nnrat-at-most 'mean (ucb 'mean 'weight 'uncertainty)))
   :value
   (function/lam
    [['mean nnrat] ['weight nnrat] ['uncertainty nnrat]]
    ;; acquisition unfolds to mean + weight*uncertainty; one application
    ;; of the general additive upper-bound law.
    (function/app (function/const* 'nnrat/at-most-add-right [])
                  'mean (nnrat-multiply 'weight 'uncertainty)))})

(def theorem-specs
  [acquisition-unfold-spec acquisition-example-spec optimism-spec
   optimism-universal-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-upper])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-ucb (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.ucb))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
