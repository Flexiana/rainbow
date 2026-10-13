(ns rainbow.algorithms.proofs.ahof.lis
  "AHoF Longest Increasing Subsequence (LIS): find the length of the longest
  strictly-increasing subsequence of a sequence -- underlying diff/patience
  sorting, box-stacking, and scheduling. Patience sorting achieves O(n log n) by
  maintaining piles of increasing tails and, for each element, either extending the
  active subsequence when the element exceeds the current tail, or replacing the
  smallest tail that is at least the element. The extend decision is:

      extends? tail element = decide (tail <= element)

  (the element extends the run when it is at least the current tail), over
  exact-rational keys. Proved native and axiom-free: the extend test; that an
  element at least the tail extends the subsequence; the certificate that an
  extending element really is at least the tail (native nnrat/at-most) -- keeping
  the run increasing; and that a smaller element cannot extend it (it starts a new
  pile). The pile bookkeeping / binary search is executable; what is proved is the
  extend decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.lis`
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

(defn- extends? [tail element]
  (function/app (function/const* 'lis/extends? []) tail element))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; extends? tail element = decide (tail <= element)
(def extends-spec
  {:name 'lis/extends? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['tail nnrat] ['element nnrat]]
                        (decide-at-most 'tail 'element))})

(def definition-specs [extends-spec])

;; Theorems -----------------------------------------------------------------

;; An element 7 at least the current tail 5 extends the increasing subsequence.
(def element-extends-run-spec
  {:name 'lis/element-extends-run :universes []
   :type (equality bool (extends? (whole 5) (whole 7))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (extends? (whole 5) (whole 7)))})

;; Certificate: an extending element is at least the tail (5 <= 7), keeping the
;; run increasing.
(def extension-keeps-increasing-spec
  {:name 'lis/extension-keeps-increasing :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; An element 3 below the tail 5 cannot extend the run (it starts a new pile).
(def smaller-element-cannot-extend-spec
  {:name 'lis/smaller-element-cannot-extend :universes []
   :type (equality bool (extends? (whole 5) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (extends? (whole 5) (whole 3)))})

(def theorem-specs
  [element-extends-run-spec extension-keeps-increasing-spec
   smaller-element-cannot-extend-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-lis
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
