(ns rainbow.algorithms.proofs.ahof.mutation-testing
  "AHoF V-family Mutation Testing: assess a test suite's fault-detection power by
  seeding many small program mutants and measuring how many the suite KILLS
  (detects). The mutation score is the exact rational fraction of killed mutants,
  and the suite is adequate when it meets a target threshold:

      mutation-score killed total = killed / total
      adequate? score threshold   = decide (threshold <= score)

  over exact rationals. Proved native and axiom-free: the score formula; a worked
  score; the adequacy decision; the certificate that an adequate suite really
  meets the threshold (threshold <= score as native nnrat/at-most); and that a
  suite below the target is inadequate. The mutant generation and the test runs
  are executable; what is proved is the mutation-score and adequacy decision.

  Requires nnrat/divide (rational-division capability, composed here),
  audit/decide-nnrat-at-most, nnrat/at-most, nnrat/decide-at-most-true-sound
  (D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mutation-testing`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- mutation-score [killed total]
  (function/app (function/const* 'mutation/score []) killed total))
(defn- adequate? [score threshold]
  (function/app (function/const* 'mutation/adequate? []) score threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; mutation-score killed total = killed / total
(def score-spec
  {:name 'mutation/score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['killed nnrat] ['total nnrat]]
                        (nnrat-divide 'killed 'total))})

;; adequate? score threshold = decide (threshold <= score)
(def adequate-spec
  {:name 'mutation/adequate? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['score nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'score))})

(def definition-specs [score-spec adequate-spec])

;; Theorems -----------------------------------------------------------------

;; 3 of 4 mutants killed -> mutation score 3/4.
(def score-example-spec
  {:name 'mutation/score-example :universes []
   :type (equality nnrat (mutation-score (whole 3) (whole 4)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (mutation-score (whole 3) (whole 4)))})

;; A suite scoring 3/4 meets the target threshold 1/2 -> adequate.
(def adequate-when-above-spec
  {:name 'mutation/adequate-when-above :universes []
   :type (equality bool (adequate? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (adequate? (fraction 3 3) (fraction 1 1)))})

;; Certificate: an adequate suite's threshold is at most its score (1/2 <= 3/4).
(def adequate-meets-threshold-spec
  {:name 'mutation/adequate-meets-threshold :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; A suite scoring 1/4 (below target 1/2) is inadequate.
(def inadequate-when-below-spec
  {:name 'mutation/inadequate-when-below :universes []
   :type (equality bool (adequate? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (adequate? (fraction 1 3) (fraction 1 1)))})

(def theorem-specs
  [score-example-spec adequate-when-above-spec adequate-meets-threshold-spec
   inadequate-when-below-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-mutation-testing (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.mutation-testing))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
