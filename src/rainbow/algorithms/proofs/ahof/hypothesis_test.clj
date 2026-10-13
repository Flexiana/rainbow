(ns rainbow.algorithms.proofs.ahof.hypothesis-test
  "AHoF Statistical Hypothesis Testing (z-test / critical-value decision): decide
  whether observed data are inconsistent with a null hypothesis at a chosen
  significance level. Having computed a test statistic (e.g. a z-score) and the
  critical value for the significance level alpha, the null is REJECTED exactly
  when the statistic reaches the critical value:

      reject-null? statistic critical = decide (critical <= statistic)

  over exact-rational values. Proved native and axiom-free: the rejection
  decision; that a statistic in the critical region rejects the null; the
  certificate that a rejection really means the statistic met the critical value
  (native nnrat/at-most) -- so the Type-I error rate is controlled at alpha; and
  that a statistic below the critical value fails to reject (insufficient
  evidence). The statistic and critical-value computation are executable; what is
  proved is the reject/fail-to-reject decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hypothesis-test`
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

(defn- reject-null? [statistic critical]
  (function/app (function/const* 'hypothesis-test/reject-null? []) statistic critical))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; reject-null? statistic critical = decide (critical <= statistic)
(def reject-null-spec
  {:name 'hypothesis-test/reject-null? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['statistic nnrat] ['critical nnrat]]
                        (decide-at-most 'critical 'statistic))})

(def definition-specs [reject-null-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A statistic of 3 reaching the critical value 2 rejects the null hypothesis.
(def rejects-in-critical-region-spec
  {:name 'hypothesis-test/rejects-in-critical-region :universes []
   :type (equality bool (reject-null? (whole 3) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (reject-null? (whole 3) (whole 2)))})

;; Certificate: a rejection means the statistic met the critical value (2 <= 3),
;; so the significance level bounds the Type-I error rate.
(def rejection-meets-critical-spec
  {:name 'hypothesis-test/rejection-meets-critical :universes []
   :type (nnrat-at-most (whole 2) (whole 3))
   :value (at-most-proof (whole 2) (whole 3))})

;; A statistic of 1 below the critical value 2 fails to reject the null.
(def fails-to-reject-spec
  {:name 'hypothesis-test/fails-to-reject :universes []
   :type (equality bool (reject-null? (whole 1) (whole 2))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (reject-null? (whole 1) (whole 2)))})

(def theorem-specs
  [rejects-in-critical-region-spec rejection-meets-critical-spec
   fails-to-reject-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-hypothesis-test (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.hypothesis-test))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
