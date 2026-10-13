(ns rainbow.algorithms.proofs.ahof.radix-sort
  "AHoF Radix Sort (LSD): sort fixed-width integer keys in O(n * d) without
  comparing whole keys -- process the digits from LEAST to most significant, and on
  each pass STABLY sort by that digit only. Stability is what makes it correct: a
  later pass on a higher digit preserves the order established by earlier passes on
  lower digits WITHIN each group of keys sharing that higher digit (not globally:
  units sorting gives [21,12], and the tens pass reorders it to [12,21]). The
  per-digit ordering decision is:

      digit-precedes? digit-a digit-b = decide (digit-a <= digit-b)

  over exact-rational (integer) digit values. Proved native and axiom-free: the
  digit-order test and worked instances on concrete digits -- digit 2 precedes
  digit 7; the worked certificate 2 <= 7 as a native nnrat/at-most; and digit 7
  does not precede digit 2. The digit extraction and the stable per-digit sort
  (e.g. counting sort) are executable; what is proved is the per-digit ordering
  decision at these instances. That each stable pass sorts by its digit, and the
  correctness of LSD radix sort, are classical and not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.radix-sort`
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

(defn- digit-precedes? [digit-a digit-b]
  (function/app (function/const* 'radix-sort/digit-precedes? []) digit-a digit-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; digit-precedes? digit-a digit-b = decide (digit-a <= digit-b)
(def digit-precedes-spec
  {:name 'radix-sort/digit-precedes? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['digit-a nnrat] ['digit-b nnrat]]
                        (decide-at-most 'digit-a 'digit-b))})

(def definition-specs [digit-precedes-spec])

;; Theorems -----------------------------------------------------------------

;; A key with digit 2 precedes one with digit 7 on this pass.
(def smaller-digit-precedes-spec
  {:name 'radix-sort/smaller-digit-precedes :universes []
   :type (equality bool (digit-precedes? (whole 2) (whole 7))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (digit-precedes? (whole 2) (whole 7)))})

;; Worked certificate: digit 2 <= digit 7.
(def preceding-digit-at-most-spec
  {:name 'radix-sort/preceding-digit-at-most :universes []
   :type (nnrat-at-most (whole 2) (whole 7))
   :value (at-most-proof (whole 2) (whole 7))})

;; A key with digit 7 follows one with digit 2 on this pass.
(def larger-digit-follows-spec
  {:name 'radix-sort/larger-digit-follows :universes []
   :type (equality bool (digit-precedes? (whole 7) (whole 2))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (digit-precedes? (whole 7) (whole 2)))})

(def theorem-specs
  [smaller-digit-precedes-spec preceding-digit-at-most-spec
   larger-digit-follows-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-radix-sort (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.radix-sort))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
