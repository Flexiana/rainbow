(ns rainbow.algorithms.proofs.ahof.bayes-theorem
  "AHoF Bayes' Theorem: invert a conditional probability to obtain the posterior
  belief in a hypothesis H after observing evidence E,

      posterior likelihood prior evidence = (likelihood * prior) / evidence
        i.e.  P(H|E) = P(E|H) P(H) / P(E),

  the foundation of Bayesian inference, diagnosis, and spam filtering. Proved
  native and axiom-free: the posterior as the normalized product of likelihood and
  prior (composing nnrat/multiply and exact rational division); a worked posterior
  (stated as rational equivalence via the cross-product certificate, since the
  quotient is not in lowest terms); and that when likelihood equals evidence the
  posterior equals the prior (the evidence is uninformative). The likelihood,
  prior, and marginal-evidence estimates are executable; what is proved is the
  posterior combination.

  Requires nnrat/multiply, nnrat/divide (rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayes-theorem`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- nnrat-equivalent [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- numerator-of [v]
  (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator-of [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-multiply [a b]
  (function/app (function/const* 'nat/multiply []) a b))
(defn- equivalent-proof [a b]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (nat-multiply (numerator-of a) (denominator-of b))))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- posterior [likelihood prior evidence]
  (function/app (function/const* 'bayes/posterior []) likelihood prior evidence))

;; Definitions --------------------------------------------------------------

;; posterior likelihood prior evidence = (likelihood * prior) / evidence
(def posterior-spec
  {:name 'bayes/posterior :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['likelihood nnrat] ['prior nnrat] ['evidence nnrat]]
                        (nnrat-divide (nnrat-multiply 'likelihood 'prior)
                                      'evidence))})

(def definition-specs [posterior-spec])

;; Theorems -----------------------------------------------------------------

;; P(E|H)=3/4, P(H)=1/2, P(E)=3/8 -> posterior = (3/8)/(3/8) = 1 (certain).
(def posterior-example-spec
  {:name 'bayes/posterior-example :universes []
   :type (nnrat-equivalent
          (posterior (fraction 3 3) (fraction 1 1) (fraction 3 7))
          (whole 1))
   :value (equivalent-proof
           (posterior (fraction 3 3) (fraction 1 1) (fraction 3 7))
           (whole 1))})

;; When the likelihood equals the evidence, the posterior equals the prior
;; (uninformative evidence): (1/2 * 3/4) / (1/2) = 3/4.
(def uninformative-evidence-spec
  {:name 'bayes/uninformative-evidence :universes []
   :type (nnrat-equivalent
          (posterior (fraction 1 1) (fraction 3 3) (fraction 1 1))
          (fraction 3 3))
   :value (equivalent-proof
           (posterior (fraction 1 1) (fraction 3 3) (fraction 1 1))
           (fraction 3 3))})

(def theorem-specs [posterior-example-spec uninformative-evidence-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-bayes-theorem
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
