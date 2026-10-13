(ns rainbow.algorithms.proofs.ahof.dutch-flag
  "AHoF Dutch National Flag (Dijkstra's 3-way partition): partition an array around
  a pivot into three regions -- less than, equal to, and greater than -- in a single
  O(n) pass with O(1) extra space. It powers 3-way quicksort (fast on many
  duplicates) and the classic 0/1/2 sort. Each element is routed by comparing it to
  the pivot; the 'goes to the low region' test is:

      goes-low? element pivot = decide (element <= pivot-minus-one)

  i.e. element < pivot (via the predecessor of the pivot, so equal elements stay in
  the middle), over exact-rational (integer) keys. Proved native and axiom-free: the
  low-region test; that an element strictly below the pivot goes to the low region;
  the certificate that a low-region element is at most the pivot's predecessor
  (native nnrat/at-most), hence strictly less than the pivot; and that an element at
  the pivot value does not go low (it stays in the equal region). The three-pointer
  swap scan is executable; what is proved is the low-region routing decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.dutch-flag`
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

(defn- goes-low? [element pivot-minus-one]
  (function/app (function/const* 'dutch-flag/goes-low? []) element pivot-minus-one))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; goes-low? element pivot-minus-one = decide (element <= pivot-minus-one)
(def goes-low-spec
  {:name 'dutch-flag/goes-low? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['element nnrat] ['pivot-minus-one nnrat]]
                        (decide-at-most 'element 'pivot-minus-one))})

(def definition-specs [goes-low-spec])

;; Theorems -----------------------------------------------------------------

;; With pivot 5 (predecessor 4), an element 2 goes to the low region.
(def below-pivot-goes-low-spec
  {:name 'dutch-flag/below-pivot-goes-low :universes []
   :type (equality bool (goes-low? (whole 2) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (goes-low? (whole 2) (whole 4)))})

;; Certificate: a low-region element is at most the pivot's predecessor (2 <= 4),
;; hence strictly less than the pivot.
(def low-element-below-pivot-spec
  {:name 'dutch-flag/low-element-below-pivot :universes []
   :type (nnrat-at-most (whole 2) (whole 4))
   :value (at-most-proof (whole 2) (whole 4))})

;; An element 5 equal to the pivot does not go low (5 > predecessor 4): it stays
;; in the equal region.
(def equal-element-stays-middle-spec
  {:name 'dutch-flag/equal-element-stays-middle :universes []
   :type (equality bool (goes-low? (whole 5) (whole 4))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (goes-low? (whole 5) (whole 4)))})

(def theorem-specs
  [below-pivot-goes-low-spec low-element-below-pivot-spec
   equal-element-stays-middle-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-dutch-flag (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.dutch-flag))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
