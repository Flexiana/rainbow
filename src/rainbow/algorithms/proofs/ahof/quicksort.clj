(ns rainbow.algorithms.proofs.ahof.quicksort
  "AHoF Quicksort: an in-place, average-case O(n log n) comparison sort by
  divide-and-conquer -- pick a pivot, PARTITION the remaining elements into those
  at most the pivot and those greater, then recursively sort each side. The
  partition decision that routes each element is:

      goes-left? element pivot = decide (element <= pivot)

  (elements at most the pivot go to the left partition), over exact-rational keys.
  Proved native and axiom-free: the partition decision; that an element at most the
  pivot goes left; the certificate that a left-partition element really is at most
  the pivot (native nnrat/at-most) -- so after recursion the whole array is sorted;
  and that an element greater than the pivot goes right. The pivot choice, the
  in-place swaps, and the recursion are executable; what is proved is the partition
  comparison decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.quicksort`
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

(defn- goes-left? [element pivot]
  (function/app (function/const* 'quicksort/goes-left? []) element pivot))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; goes-left? element pivot = decide (element <= pivot)
(def goes-left-spec
  {:name 'quicksort/goes-left? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['element nnrat] ['pivot nnrat]]
                        (decide-at-most 'element 'pivot))})

(def definition-specs [goes-left-spec])

;; Theorems -----------------------------------------------------------------

;; An element 3 at most the pivot 5 goes to the left partition.
(def small-goes-left-spec
  {:name 'quicksort/small-goes-left :universes []
   :type (equality bool (goes-left? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (goes-left? (whole 3) (whole 5)))})

;; Certificate: a left-partition element is at most the pivot (3 <= 5), so the
;; left side stays below the pivot after recursion.
(def left-partition-below-pivot-spec
  {:name 'quicksort/left-partition-below-pivot :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; An element 8 greater than the pivot 5 goes to the right partition.
(def large-goes-right-spec
  {:name 'quicksort/large-goes-right :universes []
   :type (equality bool (goes-left? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (goes-left? (whole 8) (whole 5)))})

(def theorem-specs
  [small-goes-left-spec left-partition-below-pivot-spec large-goes-right-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-quicksort (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.quicksort))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
