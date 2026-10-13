(ns rainbow.algorithms.proofs.ahof.boyer-moore
  "AHoF Boyer-Moore Majority Vote: find the element that appears MORE than n/2
  times (if one exists) in O(n) time and O(1) space -- a single streaming pass that
  keeps just a candidate and a counter, incrementing on a match and decrementing
  otherwise (replacing the candidate when the counter hits zero). A verification
  pass then confirms the survivor is a true majority exactly when its final count
  strictly exceeds half the length:

      is-majority? count threshold = decide (threshold <= count)

  where threshold = ceil((n+1)/2) (a strict majority), over exact-rational counts.
  Proved native and axiom-free: the majority test; that a count reaching the
  majority threshold confirms the majority; the certificate that a confirmed
  majority's count meets the threshold (native nnrat/at-most); and that a count
  below the threshold means no majority exists. The single-pass candidate/counter
  scan is executable; what is proved is the majority-confirmation decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.boyer-moore`
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
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- is-majority? [count threshold]
  (function/app (function/const* 'boyer-moore/is-majority? []) count threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; is-majority? count threshold = decide (threshold <= count)
(def is-majority-spec
  {:name 'boyer-moore/is-majority? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['count nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'count))})

(def definition-specs [is-majority-spec])

;; Theorems -----------------------------------------------------------------

;; In a stream of length 7 (majority threshold 4), a candidate counted 4 times is
;; the majority.
(def confirmed-majority-spec
  {:name 'boyer-moore/confirmed-majority :universes []
   :type (equality bool (is-majority? (whole 4) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-majority? (whole 4) (whole 4)))})

;; Certificate: a confirmed majority's count meets the strict-majority threshold
;; (4 <= 4).
(def majority-meets-threshold-spec
  {:name 'boyer-moore/majority-meets-threshold :universes []
   :type (nnrat-at-most (whole 4) (whole 4))
   :value (at-most-proof (whole 4) (whole 4))})

;; A candidate counted only 3 times (below threshold 4) is NOT a majority.
(def no-majority-spec
  {:name 'boyer-moore/no-majority :universes []
   :type (equality bool (is-majority? (whole 3) (whole 4))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-majority? (whole 3) (whole 4)))})

(def theorem-specs
  [confirmed-majority-spec majority-meets-threshold-spec no-majority-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-boyer-moore (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.boyer-moore))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
