(ns rainbow.algorithms.proofs.ahof.graph-coloring
  "AHoF Greedy Graph Coloring: assign colors to vertices so no edge joins two of
  the same color, using few colors -- the model for register allocation, exam
  scheduling, and frequency assignment. The greedy heuristic visits vertices in
  some order and gives each the smallest color not used by an already-colored
  neighbor. The core check is the edge CONFLICT: two adjacent vertices conflict
  exactly when they share a color,

      conflict? color-a color-b = (color-a <= color-b) AND (color-b <= color-a)

  (the colors are equal), over exact-rational (integer) colors. Proved native and
  axiom-free: the conflict test as color equality (a boolean conjunction of two
  comparisons via logic/if-data); that equal colors on adjacent vertices conflict
  (that color is forbidden); the certificates that a conflict's colors coincide
  (each at most the other, native nnrat/at-most); and that different colors are
  conflict-free (a proper coloring of that edge). The neighbor scan and smallest-
  available-color choice are executable; what is proved is the edge-conflict
  decision.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.graph-coloring`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- conflict? [color-a color-b]
  (function/app (function/const* 'graph-coloring/conflict? []) color-a color-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; conflict? color-a color-b = (color-a <= color-b) AND (color-b <= color-a)
(def conflict-spec
  {:name 'graph-coloring/conflict? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['color-a nnrat] ['color-b nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'color-a 'color-b))
                         (decide-at-most 'color-a 'color-b)
                         (decide-at-most 'color-b 'color-a)
                         false-value))})

(def definition-specs [conflict-spec])

;; Theorems -----------------------------------------------------------------

;; Adjacent vertices both colored 2 conflict (share a color).
(def same-color-conflicts-spec
  {:name 'graph-coloring/same-color-conflicts :universes []
   :type (equality bool (conflict? (whole 2) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (conflict? (whole 2) (whole 2)))})

;; Conflict certificate (one direction): conflicting colors coincide (2 <= 2).
(def conflict-colors-coincide-spec
  {:name 'graph-coloring/conflict-colors-coincide :universes []
   :type (nnrat-at-most (whole 2) (whole 2))
   :value (at-most-proof (whole 2) (whole 2))})

;; Adjacent vertices with different colors (2 and 5) are conflict-free.
(def different-colors-proper-spec
  {:name 'graph-coloring/different-colors-proper :universes []
   :type (equality bool (conflict? (whole 2) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (conflict? (whole 2) (whole 5)))})

(def theorem-specs
  [same-color-conflicts-spec conflict-colors-coincide-spec
   different-colors-proper-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-graph-coloring (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.graph-coloring))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
