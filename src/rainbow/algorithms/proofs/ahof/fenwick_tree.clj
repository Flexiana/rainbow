(ns rainbow.algorithms.proofs.ahof.fenwick-tree
  "AHoF Fenwick Tree (Binary Indexed Tree): maintain prefix sums of an array under
  point updates, both in O(log n), using a clever low-bit indexing where each index
  is responsible for a range of size equal to its lowest set bit. A prefix query
  ACCUMULATES the responsible node values while stripping the low bit off the index;
  an update adds a delta while adding the low bit. Both walk O(log n) nodes and
  combine additively:

      accumulate partial node-value = partial + node-value.

  Unlike a plain prefix-sum array (fast query, O(n) update) it supports fast
  updates, and unlike a segment tree it uses half the memory and simpler code.
  Proved native and axiom-free: the accumulation as nnrat/add; a worked prefix
  accumulation; and that accumulating the additive identity (an out-of-range node
  contributing 0) leaves the running sum unchanged. The low-bit index walks for
  query and update are executable; what is proved is the additive node combine.

  Requires nnrat/add (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fenwick-tree`
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

(defn- accumulate [partial node-value]
  (function/app (function/const* 'fenwick-tree/accumulate []) partial node-value))

;; Definitions --------------------------------------------------------------

;; accumulate partial node-value = partial + node-value
(def accumulate-spec
  {:name 'fenwick-tree/accumulate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['partial nnrat] ['node-value nnrat]]
                        (nnrat-add 'partial 'node-value))})

(def definition-specs [accumulate-spec])

;; Theorems -----------------------------------------------------------------

;; Accumulating a node value 4 onto a running prefix sum 3 gives 7.
(def accumulate-example-spec
  {:name 'fenwick-tree/accumulate-example :universes []
   :type (equality nnrat (accumulate (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (accumulate (whole 3) (whole 4)))})

;; Accumulating the additive identity (0) leaves the running sum unchanged
;; (worked at running sum 5): out-of-range nodes contribute nothing.
(def identity-node-unchanged-spec
  {:name 'fenwick-tree/identity-node-unchanged :universes []
   :type (equality nnrat (accumulate (whole 5) zero-nnrat) (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (accumulate (whole 5) zero-nnrat))})

(def theorem-specs [accumulate-example-spec identity-node-unchanged-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-fenwick-tree (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.fenwick-tree))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
