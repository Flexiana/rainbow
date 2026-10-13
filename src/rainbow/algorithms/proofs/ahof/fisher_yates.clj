(ns rainbow.algorithms.proofs.ahof.fisher-yates
  "AHoF Fisher-Yates Shuffle (Knuth shuffle): produce a UNIFORMLY RANDOM permutation
  of an array in O(n) time in place -- every one of the n! orderings is equally
  likely. Walking from the last index down to the first, position i is swapped with
  a random index j drawn from [0, i]. Correctness (uniformity) hinges on drawing j
  from exactly that range -- neither below zero nor above i -- so the swap index is
  valid exactly when it lies in [0, i]:

      valid-swap? j i = decide (j <= i)

  (with j >= 0 by construction), over exact-rational (integer) indices. Defined:
  the valid-swap test. Proved native and axiom-free, as worked instances: at i = 5
  the index 2 is valid and the index 7 is not, and the worked certificate 2 <= 5
  (native nnrat/at-most). Uniformity of the shuffle, and that the fixed suffix is
  never disturbed, are classical and not proved here. The RNG and the in-place
  swaps are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fisher-yates`
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

(defn- valid-swap? [j i]
  (function/app (function/const* 'fisher-yates/valid-swap? []) j i))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; valid-swap? j i = decide (j <= i)
(def valid-swap-spec
  {:name 'fisher-yates/valid-swap? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['j nnrat] ['i nnrat]]
                        (decide-at-most 'j 'i))})

(def definition-specs [valid-swap-spec])

;; Theorems -----------------------------------------------------------------

;; At index 5, a drawn swap index 2 (in [0,5]) is a valid swap.
(def in-range-swap-valid-spec
  {:name 'fisher-yates/in-range-swap-valid :universes []
   :type (equality bool (valid-swap? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (valid-swap? (whole 2) (whole 5)))})

;; Worked certificate 2 <= 5. That the fixed suffix is never disturbed, and the
;; shuffle's uniformity, are classical and not proved here.
(def valid-swap-within-range-spec
  {:name 'fisher-yates/valid-swap-within-range :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A swap index 7 beyond i = 5 is invalid (would disturb the fixed suffix).
(def out-of-range-swap-invalid-spec
  {:name 'fisher-yates/out-of-range-swap-invalid :universes []
   :type (equality bool (valid-swap? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (valid-swap? (whole 7) (whole 5)))})

(def theorem-specs
  [in-range-swap-valid-spec valid-swap-within-range-spec
   out-of-range-swap-invalid-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-fisher-yates
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
