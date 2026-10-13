(ns rainbow.algorithms.proofs.ahof.em
  "AHoF D13 EM Algorithm: fit latent-variable model parameters by alternating an
  E-step (compute the expected complete-data log-likelihood under the current
  parameters) and an M-step (maximize it). The defining property of EM is
  monotone ascent -- each iteration's likelihood is at least the previous one:

      improves? next-likelihood current-likelihood
        = decide (current-likelihood <= next-likelihood)

  over the exact-rational (log-)likelihoods. Proved native and axiom-free: the
  ascent test, and worked instances on concrete likelihoods -- a step from 5 to 8
  is accepted; the certificate 5 <= 8 as a native nnrat/at-most; and on equal
  likelihoods (8, 8) the test is true but shows no progress. EM's monotone ascent
  and its convergence are classical and are not proved here. The E-step
  expectation and M-step maximization are executable / pluggable concerns; what
  is proved here is the ascent test at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.em`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- improves? [next-l current-l]
  (function/app (function/const* 'em/improves? []) next-l current-l))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; improves? next current = decide (current <= next)
(def improves-spec
  {:name 'em/improves? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['next-l nnrat] ['current-l nnrat]]
                        (decide-at-most 'current-l 'next-l))})

(def definition-specs [improves-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; An EM iteration that raises the likelihood (8 from 5) is a valid ascent step.
(def iteration-ascends-spec
  {:name 'em/iteration-ascends :universes []
   :type (equality bool (improves? (whole 8) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (improves? (whole 8) (whole 5)))})

;; Worked certificate: 5 <= 8.
(def never-decreases-likelihood-spec
  {:name 'em/never-decreases-likelihood :universes []
   :type (nnrat-at-most (whole 5) (whole 8))
   :value (at-most-proof (whole 5) (whole 8))})

;; Equal likelihoods (8, 8): the test is true but shows no progress.
(def converged-at-fixed-point-spec
  {:name 'em/converged-at-fixed-point :universes []
   :type (equality bool (improves? (whole 8) (whole 8))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (improves? (whole 8) (whole 8)))})

(def theorem-specs
  [iteration-ascends-spec never-decreases-likelihood-spec
   converged-at-fixed-point-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-em (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.em))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
