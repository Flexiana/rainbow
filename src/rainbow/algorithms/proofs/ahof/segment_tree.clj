(ns rainbow.algorithms.proofs.ahof.segment-tree
  "AHoF Segment Tree: answer range-aggregate queries (sum / min / max) AND point
  updates on an array, both in O(log n), by a balanced binary tree over array
  segments in which every internal node stores the aggregate of its two children.
  For a range-SUM tree the node combine is addition:

      combine left-child right-child = left-child + right-child,

  and a range query merges the O(log n) canonical segments that cover the query
  range with the same combine. Unlike a static prefix-sum array it supports updates
  (re-combining along one root path). Proved native and axiom-free: the node
  combine as nnrat/add; a worked node value; and the identity that combining with
  the additive identity (empty segment = 0) leaves a segment's aggregate unchanged.
  The tree layout and the recursive query/update are executable; what is proved is
  the aggregate-combine at each node.

  Requires nnrat/add (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.segment-tree`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def zero-nnrat (whole 0))

(defn- combine [left-child right-child]
  (function/app (function/const* 'segment-tree/combine []) left-child right-child))

;; Definitions --------------------------------------------------------------

;; combine left-child right-child = left-child + right-child (range-sum node)
(def combine-spec
  {:name 'segment-tree/combine :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['left-child nnrat] ['right-child nnrat]]
                        (nnrat-add 'left-child 'right-child))})

(def definition-specs [combine-spec])

;; Theorems -----------------------------------------------------------------

;; A node combining children 3 and 4 stores their sum 7.
(def combine-example-spec
  {:name 'segment-tree/combine-example :universes []
   :type (equality nnrat (combine (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (combine (whole 3) (whole 4)))})

;; Combining a segment with the empty segment (identity 0) leaves it unchanged:
;; a partial query outside the range contributes nothing (worked at value 5).
(def empty-segment-identity-spec
  {:name 'segment-tree/empty-segment-identity :universes []
   :type (equality nnrat (combine zero-nnrat (whole 5)) (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (combine zero-nnrat (whole 5)))})

(def theorem-specs [combine-example-spec empty-segment-identity-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-segment-tree (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.segment-tree))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
