(ns rainbow.algorithms.proofs.ahof.expected-improvement
  "AHoF O63 Expected Improvement acquisition (Bayesian optimization). EI balances
  exploitation and exploration: the expected amount by which a candidate improves
  on the current best combines the predicted improvement (weighted by its
  probability) with the predictive uncertainty (weighted by the density at the
  best):

      ei improvement prob uncertainty density
        = improvement * prob + uncertainty * density

  over exact nonnegative rationals. The predicted improvement (mean - best), the
  standard-normal CDF prob and density (involving exp and erf), and the
  surrogate sigma (a square root) are transcendental / executable concerns -- the
  probability and density VALUES are supplied as rationals. What is proved here
  is the deterministic acquisition combination and its guarantee: EI is at least
  the exploitation term (improvement * prob <= ei), so adding the exploration
  term never reduces the acquisition below pure exploitation.

  Requires nnrat/add, nnrat/multiply, nnrat/at-most, and the decidable nnrat
  order (all in the D63 checkpoint)."
  (:require [rainbow.environment :as environment]
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

(defn- ei [improvement prob uncertainty density]
  (function/app (function/const* 'expected-improvement/ei [])
                improvement prob uncertainty density))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; ei improvement prob uncertainty density
;;   = improvement * prob + uncertainty * density
(def ei-spec
  {:name 'expected-improvement/ei :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['improvement nnrat] ['prob nnrat]
                         ['uncertainty nnrat] ['density nnrat]]
                        (nnrat-add (nnrat-multiply 'improvement 'prob)
                                   (nnrat-multiply 'uncertainty 'density)))})

(def definition-specs [ei-spec])

;; Theorems -----------------------------------------------------------------

(def ei-unfold-spec
  {:name 'expected-improvement/ei-unfold :universes []
   :type (function/forall
          [['improvement nnrat] ['prob nnrat]
           ['uncertainty nnrat] ['density nnrat]]
          (equality nnrat
                    (ei 'improvement 'prob 'uncertainty 'density)
                    (nnrat-add (nnrat-multiply 'improvement 'prob)
                               (nnrat-multiply 'uncertainty 'density))))
   :value (function/lam [['improvement nnrat] ['prob nnrat]
                         ['uncertainty nnrat] ['density nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (ei 'improvement 'prob 'uncertainty 'density)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked EI: improvement 3, prob 2, uncertainty 1, density 4 -> 3*2 + 1*4 = 10.
(def ei-example-spec
  {:name 'expected-improvement/ei-example :universes []
   :type (equality nnrat
                   (ei (whole 3) (whole 2) (whole 1) (whole 4))
                   (whole 10))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ei (whole 3) (whole 2) (whole 1) (whole 4)))})

;; The exploration term only helps: EI is at least the exploitation term
;; (improvement*prob = 6 <= ei = 10).
(def ei-at-least-exploitation-spec
  {:name 'expected-improvement/ei-at-least-exploitation :universes []
   :type (nnrat-at-most (whole 6) (ei (whole 3) (whole 2) (whole 1) (whole 4)))
   :value (at-most-proof (whole 6)
                         (ei (whole 3) (whole 2) (whole 1) (whole 4)))})

(def ei-at-least-exploitation-universal-spec
  "The UNIVERSAL guarantee: for EVERY input the expected improvement is at
  least the exploitation term improvement*prob -- the exploration term
  uncertainty*density is nonnegative, so it only helps. Upgrades the
  worked instance to an all-inputs guarantee, exploitation <=
  exploitation + 0 <= exploitation + exploration."
  {:name 'expected-improvement/ei-at-least-exploitation-universal :universes []
   :type (function/forall
          [['improvement nnrat] ['prob nnrat]
           ['uncertainty nnrat] ['density nnrat]]
          (nnrat-at-most (nnrat-multiply 'improvement 'prob)
                         (ei 'improvement 'prob 'uncertainty 'density)))
   :value
   (function/lam
    [['improvement nnrat] ['prob nnrat]
     ['uncertainty nnrat] ['density nnrat]]
    ;; ei unfolds to (improvement*prob) + (uncertainty*density); one
    ;; application of the general additive upper-bound law.
    (function/app (function/const* 'nnrat/at-most-add-right [])
                  (nnrat-multiply 'improvement 'prob)
                  (nnrat-multiply 'uncertainty 'density)))})

(def theorem-specs
  [ei-unfold-spec ei-example-spec ei-at-least-exploitation-spec
   ei-at-least-exploitation-universal-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-upper/extend-environment
      (support/extend-with :ahof-expected-improvement
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
