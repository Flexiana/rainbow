(ns rainbow.algorithms.proofs.ahof.binary-search
  "AHoF Binary Search: locate a target in a SORTED array in O(log n) by repeatedly
  halving the search interval -- comparing the target to the middle element and
  discarding the half that cannot contain it. The branch decision at each step is:

      search-left? target midpoint = decide (target <= midpoint)

  (if the target is at most the midpoint, it lies in the left half including the
  midpoint; otherwise in the right half), over exact-rational keys. Proved native
  and axiom-free: the branch test; that a target at most the midpoint searches
  left; the certificate that when it searches left the target really is at most the
  midpoint (native nnrat/at-most) so no candidate is wrongly discarded; and that a
  target above the midpoint searches right. The index arithmetic and the array
  access are executable; what is proved is the halving branch decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.binary-search`
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

(defn- search-left? [target midpoint]
  (function/app (function/const* 'binary-search/search-left? []) target midpoint))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; search-left? target midpoint = decide (target <= midpoint)
(def search-left-spec
  {:name 'binary-search/search-left? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['target nnrat] ['midpoint nnrat]]
                        (decide-at-most 'target 'midpoint))})

(def definition-specs [search-left-spec])

;; Theorems -----------------------------------------------------------------

;; A target 3 at most the midpoint 5 searches the left half.
(def small-target-searches-left-spec
  {:name 'binary-search/small-target-searches-left :universes []
   :type (equality bool (search-left? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (search-left? (whole 3) (whole 5)))})

;; Certificate: when searching left, the target is at most the midpoint (3 <= 5),
;; so the right half (all > midpoint) can be safely discarded.
(def left-branch-sound-spec
  {:name 'binary-search/left-branch-sound :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A target 8 above the midpoint 5 searches the right half.
(def large-target-searches-right-spec
  {:name 'binary-search/large-target-searches-right :universes []
   :type (equality bool (search-left? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (search-left? (whole 8) (whole 5)))})

(def theorem-specs
  [small-target-searches-left-spec left-branch-sound-spec
   large-target-searches-right-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-binary-search (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.binary-search))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
