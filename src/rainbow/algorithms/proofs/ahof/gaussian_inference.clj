(ns rainbow.algorithms.proofs.ahof.gaussian-inference
  "AHoF D9 Inference in Gaussian Models: exact closed-form conjugate updates. In
  the natural (precision) parameterization, conditioning a Gaussian on a Gaussian
  likelihood ADDS precisions -- the posterior precision is the prior precision
  plus the likelihood precision:

      posterior-precision prior likelihood = prior + likelihood

  over exact nonnegative rationals (precision = 1/variance >= 0). Proved native
  and axiom-free: the precision update, and the guarantee that observing data
  never decreases precision (prior-precision <= posterior-precision), i.e. the
  posterior is at least as certain as the prior. The posterior mean is the
  precision-weighted average of prior and observation (a division, executable);
  the variances and their square roots are executable concerns. What is proved
  here is the additive precision update and its certainty-increase guarantee.

  Requires nnrat/add, nnrat/at-most, nat/le-add-right (d63 + nat-add-order).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gaussian-inference`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- posterior-precision [prior likelihood]
  (function/app (function/const* 'gaussian/posterior-precision [])
                prior likelihood))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; posterior-precision prior likelihood = prior + likelihood
(def posterior-precision-spec
  {:name 'gaussian/posterior-precision :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['prior nnrat] ['likelihood nnrat]]
                        (nnrat-add 'prior 'likelihood))})

(def definition-specs [posterior-precision-spec])

;; Theorems -----------------------------------------------------------------

(def posterior-precision-unfold-spec
  {:name 'gaussian/posterior-precision-unfold :universes []
   :type (function/forall
          [['prior nnrat] ['likelihood nnrat]]
          (equality nnrat
                    (posterior-precision 'prior 'likelihood)
                    (nnrat-add 'prior 'likelihood)))
   :value (function/lam [['prior nnrat] ['likelihood nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (posterior-precision 'prior 'likelihood)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked update: prior precision 2, likelihood precision 3 -> 5.
(def posterior-precision-example-spec
  {:name 'gaussian/posterior-precision-example :universes []
   :type (equality nnrat
                   (posterior-precision (whole 2) (whole 3))
                   (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (posterior-precision (whole 2) (whole 3)))})

;; Certainty increases: the posterior precision is at least the prior (2 <= 5),
;; so observing data never makes the belief less certain.
(def precision-increases-spec
  {:name 'gaussian/precision-increases :universes []
   :type (nnrat-at-most (whole 2) (posterior-precision (whole 2) (whole 3)))
   :value (at-most-proof (whole 2) (posterior-precision (whole 2) (whole 3)))})

(def theorem-specs
  [posterior-precision-unfold-spec posterior-precision-example-spec
   precision-increases-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-gaussian-inference (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.gaussian-inference))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
