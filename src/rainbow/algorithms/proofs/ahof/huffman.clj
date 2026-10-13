(ns rainbow.algorithms.proofs.ahof.huffman
  "AHoF Huffman Coding: build an optimal prefix-free binary code by a greedy
  bottom-up merge. Repeatedly take the two lowest-frequency nodes, merge them into
  an internal node whose frequency is their sum, and reinsert; the merge order
  determines the codeword lengths. The two core operations are:

      merge-frequency f1 f2   = f1 + f2                 (internal node weight)
      merge-first? fa fb      = decide (fa <= fb)       (lower frequency first)

  over exact-rational symbol frequencies. Proved native and axiom-free: the merged
  frequency; a worked merge; the ordering decision that selects the lower-frequency
  node first; and the certificate for the worked pair (2 <= 5 as a native
  nnrat/at-most). Optimality of the Huffman tree (minimum expected code length)
  is classical and is not proved here. The priority queue and codeword
  assignment are executable; what is proved is the merge weight and greedy order
  at these instances.

  Requires nnrat/add, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.huffman`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
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

(defn- merge-frequency [f1 f2]
  (function/app (function/const* 'huffman/merge-frequency []) f1 f2))
(defn- merge-first? [fa fb]
  (function/app (function/const* 'huffman/merge-first? []) fa fb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; merge-frequency f1 f2 = f1 + f2
(def merge-frequency-spec
  {:name 'huffman/merge-frequency :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['f1 nnrat] ['f2 nnrat]] (nnrat-add 'f1 'f2))})

;; merge-first? fa fb = decide (fa <= fb)
(def merge-first-spec
  {:name 'huffman/merge-first? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['fa nnrat] ['fb nnrat]] (decide-at-most 'fa 'fb))})

(def definition-specs [merge-frequency-spec merge-first-spec])

;; Theorems -----------------------------------------------------------------

;; Merging nodes of frequency 2 and 3 yields an internal node of frequency 5.
(def merge-example-spec
  {:name 'huffman/merge-example :universes []
   :type (equality nnrat (merge-frequency (whole 2) (whole 3)) (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (merge-frequency (whole 2) (whole 3)))})

;; The lower-frequency node (2) is merged before the higher (5).
(def merges-lower-first-spec
  {:name 'huffman/merges-lower-first :universes []
   :type (equality bool (merge-first? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (merge-first? (whole 2) (whole 5)))})

;; Certificate for the worked pair: the node merged first has frequency at most
;; the other (2 <= 5).
(def greedy-picks-minimum-spec
  {:name 'huffman/greedy-picks-minimum :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

(def theorem-specs
  [merge-example-spec merges-lower-first-spec greedy-picks-minimum-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-huffman
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
