(ns rainbow.algorithms.proofs.ahof.binary-heap
  "AHoF Binary Heap: the array-backed complete binary tree behind the priority
  queue and heapsort, maintaining the HEAP PROPERTY -- in a min-heap every parent
  key is at most its children's keys, so the minimum is always at the root. Insert
  (sift-up) and extract-min (sift-down) restore the property in O(log n) by
  swapping a node with a child that violates it. The heap-order test between a
  parent and a child is:

      heap-ordered? parent child = decide (parent <= child)

  over exact-rational keys. Proved native and axiom-free: the heap-order test;
  worked instances on concrete keys -- a parent 2 over a child 5 is correctly
  ordered (no swap needed); the certificate 2 <= 5 as a native nnrat/at-most; and
  a parent 7 over a child 3 violates the property (sift must swap). The array
  indexing and the sift-up/down loops are executable; what is proved is the
  heap-order comparison at these instances, not the heap invariant itself.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.binary-heap`
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

(defn- heap-ordered? [parent child]
  (function/app (function/const* 'binary-heap/heap-ordered? []) parent child))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; heap-ordered? parent child = decide (parent <= child)
(def heap-ordered-spec
  {:name 'binary-heap/heap-ordered? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['parent nnrat] ['child nnrat]]
                        (decide-at-most 'parent 'child))})

(def definition-specs [heap-ordered-spec])

;; Theorems -----------------------------------------------------------------

;; A parent 2 no greater than its child 5 is correctly heap-ordered (no swap).
(def parent-below-child-ordered-spec
  {:name 'binary-heap/parent-below-child-ordered :universes []
   :type (equality bool (heap-ordered? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (heap-ordered? (whole 2) (whole 5)))})

;; Worked certificate: 2 <= 5.
(def ordered-parent-at-most-child-spec
  {:name 'binary-heap/ordered-parent-at-most-child :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A parent 7 greater than its child 3 violates the heap property (sift swaps).
(def parent-above-child-violates-spec
  {:name 'binary-heap/parent-above-child-violates :universes []
   :type (equality bool (heap-ordered? (whole 7) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (heap-ordered? (whole 7) (whole 3)))})

(def theorem-specs
  [parent-below-child-ordered-spec ordered-parent-at-most-child-spec
   parent-above-child-violates-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-binary-heap (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.binary-heap))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
