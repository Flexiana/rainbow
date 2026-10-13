(ns rainbow.algorithms.proofs.ahof.activity-selection
  "AHoF Activity Selection (greedy interval scheduling): from a set of activities
  with start and finish times, select the largest set of mutually compatible
  (non-overlapping) activities. The optimal greedy strategy sorts by finish time
  and admits each activity whose start is no earlier than the last selected
  finish:

      compatible? start last-finish = decide (last-finish <= start)

  over exact-rational times. Proved native and axiom-free: the compatibility test;
  worked instances on concrete times -- an activity starting at 5 after the last
  finish 3 is admitted; the certificate 3 <= 5 as a native nnrat/at-most; and an
  activity starting at 2 is rejected (it would overlap). The sort by finish time
  and the selection sweep are executable; what is proved is the earliest-finish
  admission decision at these instances. Optimality of the earliest-finish greedy
  (the classical exchange argument) is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.activity-selection`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- compatible? [start last-finish]
  (function/app (function/const* 'activity-selection/compatible? [])
                start last-finish))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; compatible? start last-finish = decide (last-finish <= start)
(def compatible-spec
  {:name 'activity-selection/compatible? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['start nnrat] ['last-finish nnrat]]
                        (decide-at-most 'last-finish 'start))})

(def definition-specs [compatible-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; An activity starting at 5, after the last selected finish (3), is admitted.
(def admits-compatible-activity-spec
  {:name 'activity-selection/admits-compatible-activity :universes []
   :type (equality bool (compatible? (whole 5) (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (compatible? (whole 5) (whole 3)))})

;; Worked certificate: last finish 3 <= start 5.
(def admitted-does-not-overlap-spec
  {:name 'activity-selection/admitted-does-not-overlap :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; An activity starting at 2, before the last finish (3), is rejected (overlap).
(def rejects-overlapping-activity-spec
  {:name 'activity-selection/rejects-overlapping-activity :universes []
   :type (equality bool (compatible? (whole 2) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (compatible? (whole 2) (whole 3)))})

(def theorem-specs
  [admits-compatible-activity-spec admitted-does-not-overlap-spec
   rejects-overlapping-activity-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-activity-selection
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
