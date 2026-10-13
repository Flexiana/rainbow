(ns rainbow.algorithms.proofs.ahof.two-pointers
  "AHoF Two Pointers: solve many array/string problems in a single O(n) pass by
  maintaining two indices that move toward each other (or in tandem) instead of
  nesting loops. The canonical use is finding a pair in a SORTED array that sums to
  a target: with a left and right pointer, if the current sum is too large move the
  right pointer left (to decrease), if too small move the left pointer right. The
  shrink decision is:

      shrink-right? current-sum target = decide (target <= current-sum)

  (the sum is at least the target, so shrink from the large end), over
  exact-rational values. Proved native and axiom-free: the pointer-move decision;
  that a sum at least the target shrinks from the right; the certificate that when
  shrinking, the current sum really is at least the target (native nnrat/at-most)
  -- so no smaller-sum pair is skipped; and that a sum below the target grows from
  the left. The pointer bookkeeping is executable; what is proved is the
  move-which-pointer decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.two-pointers`
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

(defn- shrink-right? [current-sum target]
  (function/app (function/const* 'two-pointers/shrink-right? []) current-sum target))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; shrink-right? current-sum target = decide (target <= current-sum)
(def shrink-right-spec
  {:name 'two-pointers/shrink-right? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['current-sum nnrat] ['target nnrat]]
                        (decide-at-most 'target 'current-sum))})

(def definition-specs [shrink-right-spec])

;; Theorems -----------------------------------------------------------------

;; A current sum 7 at least the target 5 shrinks from the right (move right left).
(def large-sum-shrinks-right-spec
  {:name 'two-pointers/large-sum-shrinks-right :universes []
   :type (equality bool (shrink-right? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (shrink-right? (whole 7) (whole 5)))})

;; Certificate: when shrinking, the current sum is at least the target (5 <= 7),
;; so no pair with a smaller sum is skipped.
(def shrink-sum-at-least-target-spec
  {:name 'two-pointers/shrink-sum-at-least-target :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A current sum 3 below the target 5 grows from the left (move left right).
(def small-sum-grows-left-spec
  {:name 'two-pointers/small-sum-grows-left :universes []
   :type (equality bool (shrink-right? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (shrink-right? (whole 3) (whole 5)))})

(def theorem-specs
  [large-sum-shrinks-right-spec shrink-sum-at-least-target-spec
   small-sum-grows-left-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-two-pointers (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.two-pointers))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
