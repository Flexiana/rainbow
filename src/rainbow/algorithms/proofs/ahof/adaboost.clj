(ns rainbow.algorithms.proofs.ahof.adaboost
  "AHoF AdaBoost (Adaptive Boosting): combine many weak classifiers into a strong
  one by a weighted majority vote, where each weak learner's vote weight
  alpha = (1/2) ln((1 - err)/err) DECREASES with its weighted error err -- more
  accurate learners get larger votes, and after each round the misclassified
  examples are up-weighted so the next learner focuses on them. The ordering of
  vote weights by error is:

      earns-more-weight? err-a err-b = decide (err-a <= err-b)

  (the lower-error learner earns at least as much weight), over exact-rational
  errors. Defined: the weight-ordering test. Proved native and axiom-free, as
  worked instances: error 1/4 earns more weight than error 1/2, error 1/2 does not
  earn more weight than error 1/4, and the worked certificate 1/4 <= 1/2 (native
  nnrat/at-most). That alpha is monotone decreasing in error, and AdaBoost's
  classical training-error bound, are not proved here. The alpha computation (a
  log), the reweighting, and the final vote are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.adaboost`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- earns-more-weight? [err-a err-b]
  (function/app (function/const* 'adaboost/earns-more-weight? []) err-a err-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; earns-more-weight? err-a err-b = decide (err-a <= err-b)
(def earns-more-weight-spec
  {:name 'adaboost/earns-more-weight? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['err-a nnrat] ['err-b nnrat]]
                        (decide-at-most 'err-a 'err-b))})

(def definition-specs [earns-more-weight-spec])

;; Theorems -----------------------------------------------------------------

;; A learner with error 1/4 earns more vote weight than one with error 1/2.
(def lower-error-earns-more-spec
  {:name 'adaboost/lower-error-earns-more :universes []
   :type (equality bool (earns-more-weight? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (earns-more-weight? (fraction 1 3) (fraction 1 1)))})

;; Worked certificate 1/4 <= 1/2. That alpha is monotone decreasing in error is
;; classical and not proved here.
(def more-weight-means-lower-error-spec
  {:name 'adaboost/more-weight-means-lower-error :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

;; A higher-error learner (1/2) does not earn more weight than a lower one (1/4).
(def higher-error-earns-less-spec
  {:name 'adaboost/higher-error-earns-less :universes []
   :type (equality bool (earns-more-weight? (fraction 1 1) (fraction 1 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (earns-more-weight? (fraction 1 1) (fraction 1 3)))})

(def theorem-specs
  [lower-error-earns-more-spec more-weight-means-lower-error-spec
   higher-error-earns-less-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-adaboost (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.adaboost))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
