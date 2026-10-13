(ns rainbow.algorithms.proofs.ahof.bin-packing
  "AHoF Bin Packing (First-Fit approximation): pack items of given sizes into the
  fewest unit-capacity bins. The First-Fit heuristic places each item into the
  first bin with enough remaining capacity, opening a new bin only if none fits;
  it is known to use at most about 1.7x the optimal number of bins (not proved
  here). An item fits a bin
  exactly when its size does not exceed the bin's remaining capacity:

      fits? item-size remaining = decide (item-size <= remaining)

  over exact-rational sizes. Proved native and axiom-free: the fit test; worked
  instances on concrete sizes -- an item of size 1/2 fits a bin with 3/4 remaining;
  the certificate 1/2 <= 3/4 as a native nnrat/at-most; and an item of size 3/4
  does not fit a bin with 1/2 remaining (a new bin must open). The bin list and
  remaining-capacity bookkeeping are executable; what is proved is the first-fit
  placement decision at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bin-packing`
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
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- fits? [size remaining]
  (function/app (function/const* 'bin-packing/fits? []) size remaining))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; fits? size remaining = decide (size <= remaining)
(def fits-spec
  {:name 'bin-packing/fits? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['size nnrat] ['remaining nnrat]]
                        (decide-at-most 'size 'remaining))})

(def definition-specs [fits-spec])

;; Theorems -----------------------------------------------------------------

;; An item of size 1/2 fits a bin with 3/4 remaining.
(def item-fits-spec
  {:name 'bin-packing/item-fits :universes []
   :type (equality bool (fits? (fraction 1 1) (fraction 3 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (fits? (fraction 1 1) (fraction 3 3)))})

;; Worked certificate: 1/2 <= 3/4.
(def placement-respects-capacity-spec
  {:name 'bin-packing/placement-respects-capacity :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; An item of size 3/4 does not fit a bin with only 1/2 remaining: open a new bin.
(def oversized-opens-new-bin-spec
  {:name 'bin-packing/oversized-opens-new-bin :universes []
   :type (equality bool (fits? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (fits? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [item-fits-spec placement-respects-capacity-spec oversized-opens-new-bin-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bin-packing
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
