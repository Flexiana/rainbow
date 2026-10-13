(ns rainbow.algorithms.proofs.edit-distance
  "AHoF edit distance / Levenshtein alignment DP cell. Aligning two sequences,
  the dynamic-programming recurrence at each cell takes the cheapest of the three
  edit operations reaching it -- deletion, insertion, or match/substitution:

      cell del ins sub = min( del, min(ins, sub) )

  over the exact-rational operation costs. This is the Needleman-Wunsch /
  Levenshtein backward recurrence. Proved native and axiom-free: worked instances
  with costs del 3, ins 5, sub 2 -- the cell is 2, and the worked certificates
  cell <= 3, cell <= 5, and cell <= 2. The alignment traceback and the full cost
  matrix are executable concerns; what is proved here is the cell recurrence at
  this instance. That the cell is at most each option for all costs, and the
  optimality of the edit-distance DP, are classical and not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all carried by the D63
  checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.edit-distance`
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- nnrat-min-term [a b] (if-value (decide-at-most a b) a b))

(defn- cell [del ins sub]
  (function/app (function/const* 'edit-distance/cell []) del ins sub))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell del ins sub = min( del, min(ins, sub) )
(def cell-spec
  {:name 'edit-distance/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['del nnrat] ['ins nnrat] ['sub nnrat]]
                        (nnrat-min-term 'del (nnrat-min-term 'ins 'sub)))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked: deletion 3, insertion 5, substitution 2 -> the DP cell is 2.
(def cell-example-spec
  {:name 'edit-distance/cell-example :universes []
   :type (equality nnrat
                   (cell (whole 3) (whole 5) (whole 2))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 3) (whole 5) (whole 2)))})

;; Worked certificate: cell 3 5 2 <= deletion cost 3.
(def cell-below-delete-spec
  {:name 'edit-distance/cell-below-delete :universes []
   :type (nnrat-at-most (cell (whole 3) (whole 5) (whole 2)) (whole 3))
   :value (at-most-proof (cell (whole 3) (whole 5) (whole 2)) (whole 3))})

;; Worked certificate: cell 3 5 2 <= insertion cost 5.
(def cell-below-insert-spec
  {:name 'edit-distance/cell-below-insert :universes []
   :type (nnrat-at-most (cell (whole 3) (whole 5) (whole 2)) (whole 5))
   :value (at-most-proof (cell (whole 3) (whole 5) (whole 2)) (whole 5))})

;; Worked certificate: cell 3 5 2 <= substitution cost 2.
(def cell-below-substitute-spec
  {:name 'edit-distance/cell-below-substitute :universes []
   :type (nnrat-at-most (cell (whole 3) (whole 5) (whole 2)) (whole 2))
   :value (at-most-proof (cell (whole 3) (whole 5) (whole 2)) (whole 2))})

(def theorem-specs
  [cell-example-spec cell-below-delete-spec cell-below-insert-spec
   cell-below-substitute-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :edit-distance (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.edit-distance))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
