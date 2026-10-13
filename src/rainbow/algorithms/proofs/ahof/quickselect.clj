(ns rainbow.algorithms.proofs.ahof.quickselect
  "AHoF Quickselect (Hoare's selection): find the k-th smallest element of an
  unsorted array in expected O(n) -- faster than sorting -- by partitioning around
  a pivot (as in quicksort) but recursing into ONLY the side that contains the
  target rank. After partitioning, the target lies in the left partition exactly
  when its rank is at most the pivot's final rank:

      recurse-left? target-rank pivot-rank = decide (target-rank <= pivot-rank)

  over exact-rational (integer) ranks. Proved native and axiom-free: the
  recursion-side decision and worked instances on concrete ranks -- target rank 2
  against pivot rank 4 recurses left; the worked certificate 2 <= 4 as a native
  nnrat/at-most; and target rank 7 against pivot rank 4 recurses right. The
  partitioning and pivot selection are executable; what is proved is the
  recurse-which-side decision at these instances. Correctness of the selection and
  its linear expected time are classical and not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.quickselect`
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

(defn- recurse-left? [target-rank pivot-rank]
  (function/app (function/const* 'quickselect/recurse-left? []) target-rank pivot-rank))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; recurse-left? target-rank pivot-rank = decide (target-rank <= pivot-rank)
(def recurse-left-spec
  {:name 'quickselect/recurse-left? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['target-rank nnrat] ['pivot-rank nnrat]]
                        (decide-at-most 'target-rank 'pivot-rank))})

(def definition-specs [recurse-left-spec])

;; Theorems -----------------------------------------------------------------

;; A target rank 2 at most the pivot rank 4 recurses into the left partition.
(def target-in-left-spec
  {:name 'quickselect/target-in-left :universes []
   :type (equality bool (recurse-left? (whole 2) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (recurse-left? (whole 2) (whole 4)))})

;; Worked certificate: target rank 2 <= pivot rank 4.
(def left-target-below-pivot-spec
  {:name 'quickselect/left-target-below-pivot :universes []
   :type (nnrat-at-most (whole 2) (whole 4))
   :value (at-most-proof (whole 2) (whole 4))})

;; A target rank 7 greater than the pivot rank 4 recurses into the right partition.
(def target-in-right-spec
  {:name 'quickselect/target-in-right :universes []
   :type (equality bool (recurse-left? (whole 7) (whole 4))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (recurse-left? (whole 7) (whole 4)))})

(def theorem-specs
  [target-in-left-spec left-target-below-pivot-spec target-in-right-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-quickselect
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
