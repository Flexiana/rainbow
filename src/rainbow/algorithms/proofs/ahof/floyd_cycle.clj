(ns rainbow.algorithms.proofs.ahof.floyd-cycle
  "AHoF Floyd's Cycle Detection (tortoise and hare): detect a cycle in a linked
  list or a functional sequence x_{n+1} = f(x_n) in O(1) extra space, by advancing a
  SLOW pointer one step and a FAST pointer two steps per iteration. If the sequence
  is eventually periodic the fast pointer laps the slow one and they land on the
  same node; if it terminates, the fast pointer runs off the end. A cycle is
  detected exactly when the two pointers MEET (occupy the same position):

      meet? slow-position fast-position
        = (slow-position <= fast-position) AND (fast-position <= slow-position)

  (the positions are equal), over exact-rational (integer) positions. Proved native
  and axiom-free: the meeting test as position equality (a boolean conjunction of
  two comparisons via logic/if-data); that equal positions signal a cycle; the
  certificates that meeting positions coincide (each at most the other, native
  nnrat/at-most); and that different positions mean no meeting yet. The two-speed
  pointer advance is executable; what is proved is the meet decision.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.floyd-cycle`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- meet? [slow-position fast-position]
  (function/app (function/const* 'floyd-cycle/meet? []) slow-position fast-position))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; meet? slow fast = (slow <= fast) AND (fast <= slow)   (positions are equal)
(def meet-spec
  {:name 'floyd-cycle/meet? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['slow-position nnrat] ['fast-position nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'slow-position 'fast-position))
                         (decide-at-most 'slow-position 'fast-position)
                         (decide-at-most 'fast-position 'slow-position)
                         false-value))})

(def definition-specs [meet-spec])

;; Theorems -----------------------------------------------------------------

;; The pointers landing on the same node (both at position 4) signal a cycle.
(def same-position-detects-cycle-spec
  {:name 'floyd-cycle/same-position-detects-cycle :universes []
   :type (equality bool (meet? (whole 4) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (meet? (whole 4) (whole 4)))})

;; Meeting certificate (one direction): the meeting positions coincide (4 <= 4).
(def meeting-positions-coincide-spec
  {:name 'floyd-cycle/meeting-positions-coincide :universes []
   :type (nnrat-at-most (whole 4) (whole 4))
   :value (at-most-proof (whole 4) (whole 4))})

;; Different positions (2 and 5) mean the pointers have not met -- no cycle
;; detected yet.
(def different-position-no-meeting-spec
  {:name 'floyd-cycle/different-position-no-meeting :universes []
   :type (equality bool (meet? (whole 2) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (meet? (whole 2) (whole 5)))})

(def theorem-specs
  [same-position-detects-cycle-spec meeting-positions-coincide-spec
   different-position-no-meeting-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-floyd-cycle
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
