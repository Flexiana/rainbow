(ns rainbow.algorithms.proofs.ahof.n-queens
  "AHoF N-Queens (backtracking constraint satisfaction): place N queens on an NxN
  board so none attacks another -- the textbook example of backtracking search,
  which extends a partial placement column by column and abandons (backtracks) any
  branch that violates a constraint. Placing one queen per column, the remaining
  conflict is the DIAGONAL attack: two queens attack diagonally exactly when their
  row distance equals their column distance,

      attacks-diagonally? row-distance col-distance
        = (row-distance <= col-distance) AND (col-distance <= row-distance)

  (i.e. the distances are equal), over exact-rational (integer) distances. Proved
  native and axiom-free: the diagonal-attack test as the equality of the two
  distances (a boolean conjunction of two comparisons via logic/if-data); that
  equal distances are a diagonal attack (the branch is pruned); the certificates
  that an attack's distances coincide (each at most the other, native
  nnrat/at-most); and that unequal distances are safe. The row placement and the
  recursive search are executable; what is proved is the diagonal-conflict decision.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.n-queens`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- attacks-diagonally? [row-distance col-distance]
  (function/app (function/const* 'n-queens/attacks-diagonally? [])
                row-distance col-distance))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; attacks-diagonally? rd cd = (rd <= cd) AND (cd <= rd)   (distances are equal)
(def attacks-diagonally-spec
  {:name 'n-queens/attacks-diagonally? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['row-distance nnrat] ['col-distance nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'row-distance 'col-distance))
                         (decide-at-most 'row-distance 'col-distance)
                         (decide-at-most 'col-distance 'row-distance)
                         false-value))})

(def definition-specs [attacks-diagonally-spec])

;; Theorems -----------------------------------------------------------------

;; Queens 3 rows and 3 columns apart attack diagonally (equal distances).
(def equal-distance-attacks-spec
  {:name 'n-queens/equal-distance-attacks :universes []
   :type (equality bool (attacks-diagonally? (whole 3) (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (attacks-diagonally? (whole 3) (whole 3)))})

;; Attack certificate (one direction): a diagonal attack has row-distance at most
;; the column-distance (3 <= 3).
(def attack-distances-coincide-spec
  {:name 'n-queens/attack-distances-coincide :universes []
   :type (nnrat-at-most (whole 3) (whole 3))
   :value (at-most-proof (whole 3) (whole 3))})

;; Queens 3 rows but 5 columns apart do NOT attack diagonally (safe placement).
(def unequal-distance-safe-spec
  {:name 'n-queens/unequal-distance-safe :universes []
   :type (equality bool (attacks-diagonally? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (attacks-diagonally? (whole 3) (whole 5)))})

(def theorem-specs
  [equal-distance-attacks-spec attack-distances-coincide-spec
   unequal-distance-safe-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-n-queens
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
