(ns rainbow.algorithms.proofs.histogram-bin
  "AHoF histogram / kernel-density bin count: the number of sample values that
  fall inside a half-open-style bin [lo, hi],

      count-in-range lo hi xs = |{ x in xs : lo <= x and x <= hi }|,

  the primitive behind histograms and (boxcar-kernel) density estimation. It is a
  fold over the sample list that increments a natural counter exactly when both
  decidable rational comparisons hold, expressed as nested if-data (no boolean
  connective needed):

      count (x :: rest) = if (lo <= x) then (if (x <= hi) then succ (count rest)
                                                          else count rest)
                                       else count rest.

  Exact naturals and the decidable rational order, so the bin count is proved
  data. Sweeping bins into a full histogram or normalizing into a density is an
  executable concern; what is proved here is the bin-count fold and worked
  counts.

  Requires nat, the decidable nnrat order (audit/decide-nnrat-at-most),
  logic/if-data, and data/List.rec (all carried by the D63 checkpoint).

  Scope (measured by the kernel): this module has 1 worked instances (statements about specific values) and 3 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.histogram-bin`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat (function/app (function/const* 'data/List [type-level]) nnrat))
(def zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-nat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nat (condition decision) decision then-value else-value))

(defn- count-in-range [lo hi xs]
  (function/app (function/const* 'histogram/count-in-range []) lo hi xs))

;; Definitions --------------------------------------------------------------

;; count-in-range lo hi xs = fold (increment when lo <= x <= hi) 0 xs
(def count-in-range-spec
  {:name 'histogram/count-in-range :kind :definition :universes []
   :type (function/arrow nnrat nnrat list-nnrat nat)
   :value
   (function/lam
    [['lo nnrat] ['hi nnrat] ['xs list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nat)
     zero
     (function/lam
      [['head nnrat] ['tail list-nnrat] ['tail-count nat]]
      (if-nat (decide-at-most 'lo 'head)
              (if-nat (decide-at-most 'head 'hi)
                      (succ 'tail-count)
                      'tail-count)
              'tail-count))
     'xs))})

(def definition-specs [count-in-range-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- sample-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail))
          (function/app (function/const* 'data/nil [type-level]) nnrat)
          (reverse elements)))

;; Prepending an in-bin value (4 in [2,6]) increments the count.
(def cons-in-bin-increments-spec
  {:name 'histogram/cons-in-bin-increments :universes []
   :type (function/forall
          [['xs list-nnrat]]
          (equality nat
                    (count-in-range (whole 2) (whole 6)
                                    (cons-nnrat (whole 4) 'xs))
                    (succ (count-in-range (whole 2) (whole 6) 'xs))))
   :value (function/lam
           [['xs list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (count-in-range (whole 2) (whole 6)
                                (cons-nnrat (whole 4) 'xs))))})

;; Prepending a below-bin value (1 < 2) leaves the count unchanged.
(def cons-below-bin-preserves-spec
  {:name 'histogram/cons-below-bin-preserves :universes []
   :type (function/forall
          [['xs list-nnrat]]
          (equality nat
                    (count-in-range (whole 2) (whole 6)
                                    (cons-nnrat (whole 1) 'xs))
                    (count-in-range (whole 2) (whole 6) 'xs)))
   :value (function/lam
           [['xs list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (count-in-range (whole 2) (whole 6)
                                (cons-nnrat (whole 1) 'xs))))})

;; Prepending an above-bin value (7 > 6) leaves the count unchanged.
(def cons-above-bin-preserves-spec
  {:name 'histogram/cons-above-bin-preserves :universes []
   :type (function/forall
          [['xs list-nnrat]]
          (equality nat
                    (count-in-range (whole 2) (whole 6)
                                    (cons-nnrat (whole 7) 'xs))
                    (count-in-range (whole 2) (whole 6) 'xs)))
   :value (function/lam
           [['xs list-nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (count-in-range (whole 2) (whole 6)
                                (cons-nnrat (whole 7) 'xs))))})

;; Worked: of [1,4,7,5], two values (4,5) lie in the bin [2,6].
(def count-example-spec
  {:name 'histogram/count-example :universes []
   :type (equality nat
                   (count-in-range (whole 2) (whole 6)
                                   (sample-list (whole 1) (whole 4)
                                                (whole 7) (whole 5)))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (count-in-range (whole 2) (whole 6)
                                        (sample-list (whole 1) (whole 4)
                                                     (whole 7) (whole 5))))})

(def theorem-specs
  [cons-in-bin-increments-spec cons-below-bin-preserves-spec
   cons-above-bin-preserves-spec count-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :histogram-bin
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
