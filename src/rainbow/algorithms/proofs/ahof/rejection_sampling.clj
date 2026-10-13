(ns rainbow.algorithms.proofs.ahof.rejection-sampling
  "AHoF V21 Rejection Sampling (for failure events): draw samples and keep only
  those consistent with the evidence / that hit the target event, rejecting the
  rest. A sample is accepted when its statistic is within the evidence tolerance:

      accepts? statistic tolerance = decide (statistic <= tolerance)

  over the decidable rational order. Proved native and axiom-free: the acceptance
  test and worked instances on concrete values -- statistic 2 against tolerance 5
  is accepted; the worked certificate 2 <= 5 as a native nnrat/at-most; and
  statistic 8 against tolerance 5 is rejected. The proposal draws and the
  acceptance ratio (fraction retained) are executable concerns; what is proved
  here is the acceptance decision at these instances. That the retained samples
  form a valid conditional sample is the classical property of rejection sampling
  and is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most, and
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rejection-sampling`
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

(defn- accepts? [statistic tolerance]
  (function/app (function/const* 'rejection/accepts? []) statistic tolerance))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; accepts? statistic tolerance = decide (statistic <= tolerance)
(def accepts-spec
  {:name 'rejection/accepts? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['statistic nnrat] ['tolerance nnrat]]
                        (decide-at-most 'statistic 'tolerance))})

(def definition-specs [accepts-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A within-tolerance sample (2 <= 5) is accepted.
(def accepts-consistent-spec
  {:name 'rejection/accepts-consistent :universes []
   :type (equality bool (accepts? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts? (whole 2) (whole 5)))})

;; Worked certificate: statistic 2 <= tolerance 5.
(def accepted-is-valid-spec
  {:name 'rejection/accepted-is-valid :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; An out-of-tolerance sample (8 > 5) is rejected.
(def rejects-inconsistent-spec
  {:name 'rejection/rejects-inconsistent :universes []
   :type (equality bool (accepts? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts? (whole 8) (whole 5)))})

(def theorem-specs
  [accepts-consistent-spec accepted-is-valid-spec rejects-inconsistent-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-rejection-sampling (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.rejection-sampling))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
