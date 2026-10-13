(ns rainbow.algorithms.proofs.ahof.lcs
  "AHoF Longest Common Subsequence (dynamic programming): the length of the
  longest subsequence common to two sequences -- the basis of diff, version
  control merges, and bioinformatics alignment. The DP recurrence: if the current
  characters MATCH, extend the diagonal subproblem by one; otherwise take the best
  of dropping a character from either sequence (the left or upper neighbor):

      cell matched? diag left up
        = if matched? then 1 + diag else max(left, up)

  over exact-rational subproblem lengths. Proved native and axiom-free: the DP
  cell composing a match branch (logic/if-data on the match bit), a successor on
  the diagonal, and the decidable rational max of the two neighbors; a worked
  match cell; a worked mismatch cell; and the certificate that a mismatch cell
  dominates both neighbors (native nnrat/at-most). The character comparison and the
  table sweep are executable; what is proved is the LCS recurrence cell.

  Requires nnrat/add, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.lcs`
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
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nnrat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def one-nnrat (whole 1))

;; nnrat-max via if-data (inlined)
(defn- nnrat-max [a b]
  (if-nnrat (decide-at-most a b) b a))

(defn- cell [matched diag left up]
  (function/app (function/const* 'lcs/cell []) matched diag left up))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell matched diag left up = if matched then 1+diag else max(left, up)
(def cell-spec
  {:name 'lcs/cell :kind :definition :universes []
   :type (function/arrow bool nnrat nnrat nnrat nnrat)
   :value (function/lam [['matched bool] ['diag nnrat] ['left nnrat] ['up nnrat]]
                        (if-nnrat 'matched
                                  (nnrat-add one-nnrat 'diag)
                                  (nnrat-max 'left 'up)))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

;; On a match with diagonal length 2, the cell extends to 3.
(def match-extends-diagonal-spec
  {:name 'lcs/match-extends-diagonal :universes []
   :type (equality nnrat (cell true-value (whole 2) (whole 9) (whole 9))
                   (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell true-value (whole 2) (whole 9) (whole 9)))})

;; On a mismatch with neighbors 2 (left) and 3 (up), the cell is max = 3.
(def mismatch-takes-max-spec
  {:name 'lcs/mismatch-takes-max :universes []
   :type (equality nnrat (cell false-value (whole 5) (whole 2) (whole 3))
                   (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell false-value (whole 5) (whole 2) (whole 3)))})

;; Certificate: the mismatch cell dominates the left neighbor (2 <= 3).
(def dominates-left-neighbor-spec
  {:name 'lcs/dominates-left-neighbor :universes []
   :type (nnrat-at-most (whole 2) (whole 3))
   :value (at-most-proof (whole 2) (whole 3))})

(def theorem-specs
  [match-extends-diagonal-spec mismatch-takes-max-spec
   dominates-left-neighbor-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-lcs
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
