(ns rainbow.algorithms.proofs.ahof.merge-sort
  "AHoF Merge Sort: a stable, worst-case O(n log n) comparison sort by
  divide-and-conquer -- split the list in half, recursively sort each half, then
  MERGE the two sorted halves. The merge repeatedly emits the smaller of the two
  current heads; the decision (taking the left head on a tie keeps the sort
  stable) is:

      take-from-left? left-head right-head = decide (left-head <= right-head)

  over exact-rational keys. Proved native and axiom-free, as worked instances: left
  head 2 against right head 5 takes from the left; the worked certificate 2 <= 5
  (native nnrat/at-most); and left head 7 against right head 3 yields to the
  right. That merge sort is correct and stable, and that the merged output stays
  sorted, are classical and not proved here; the split, recursion, and list
  plumbing are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.merge-sort`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- take-from-left? [left-head right-head]
  (function/app (function/const* 'merge-sort/take-from-left? []) left-head right-head))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; take-from-left? left-head right-head = decide (left-head <= right-head)
(def take-from-left-spec
  {:name 'merge-sort/take-from-left? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['left-head nnrat] ['right-head nnrat]]
                        (decide-at-most 'left-head 'right-head))})

(def definition-specs [take-from-left-spec])

;; Theorems -----------------------------------------------------------------

;; When the left head 2 is at most the right head 5, emit the left element.
(def emits-smaller-left-spec
  {:name 'merge-sort/emits-smaller-left :universes []
   :type (equality bool (take-from-left? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (take-from-left? (whole 2) (whole 5)))})

;; Worked certificate for the emission above: 2 <= 5 (sortedness of the merged
;; output is classical, not proved here).
(def emitted-keeps-order-spec
  {:name 'merge-sort/emitted-keeps-order :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A larger left head 7 yields to the right head 3.
(def larger-left-yields-spec
  {:name 'merge-sort/larger-left-yields :universes []
   :type (equality bool (take-from-left? (whole 7) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (take-from-left? (whole 7) (whole 3)))})

(def theorem-specs
  [emits-smaller-left-spec emitted-keeps-order-spec larger-left-yields-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-merge-sort
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
