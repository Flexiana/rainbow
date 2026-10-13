(ns rainbow.algorithms.proofs.floyd-warshall
  "AHoF Floyd-Warshall all-pairs shortest paths -- the dynamic-programming
  relaxation through an intermediate node. Allowing paths to route through node
  k, the shortest i->j distance is the better of the current direct estimate and
  the detour i->k->j:

      cell direct dik dkj = min( direct, dik + dkj )

  over exact-rational edge weights. Proved native and axiom-free: worked instances
  with direct 10 and detour 3 + 4 -- the cell relaxes to 7, and the worked
  certificates cell <= 10 and cell <= 3 + 4. The triple loop over (k, i, j) that
  fills the full distance matrix is an executable concern; what is proved here is
  the relaxation cell at this instance. That relaxation never worsens for all
  weights, and the correctness of Floyd-Warshall, are classical and not proved
  here.

  Requires nnrat/at-most, nnrat/add, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.floyd-warshall`
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
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- nnrat-min-term [a b] (if-value (decide-at-most a b) a b))

(defn- cell [direct dik dkj]
  (function/app (function/const* 'floyd-warshall/cell []) direct dik dkj))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; cell direct dik dkj = min( direct, dik + dkj )
(def cell-spec
  {:name 'floyd-warshall/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['direct nnrat] ['dik nnrat] ['dkj nnrat]]
                        (nnrat-min-term 'direct (nnrat-add 'dik 'dkj)))})

(def definition-specs [cell-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked: direct edge 10, detour 3 + 4 = 7 -> the cell relaxes to 7.
(def cell-relaxes-spec
  {:name 'floyd-warshall/cell-relaxes :universes []
   :type (equality nnrat
                   (cell (whole 10) (whole 3) (whole 4))
                   (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (whole 10) (whole 3) (whole 4)))})

;; Worked certificate: cell 10 3 4 <= direct 10.
(def cell-below-direct-spec
  {:name 'floyd-warshall/cell-below-direct :universes []
   :type (nnrat-at-most (cell (whole 10) (whole 3) (whole 4)) (whole 10))
   :value (at-most-proof (cell (whole 10) (whole 3) (whole 4)) (whole 10))})

;; Worked certificate: cell 10 3 4 <= detour 3 + 4.
(def cell-below-detour-spec
  {:name 'floyd-warshall/cell-below-detour :universes []
   :type (nnrat-at-most (cell (whole 10) (whole 3) (whole 4))
                        (nnrat-add (whole 3) (whole 4)))
   :value (at-most-proof (cell (whole 10) (whole 3) (whole 4))
                         (nnrat-add (whole 3) (whole 4)))})

(def theorem-specs
  [cell-relaxes-spec cell-below-direct-spec cell-below-detour-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :floyd-warshall
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
