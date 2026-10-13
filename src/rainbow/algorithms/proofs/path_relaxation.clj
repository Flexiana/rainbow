(ns rainbow.algorithms.proofs.path-relaxation
  "AHoF shortest-path edge relaxation (the core step of Bellman-Ford and
  Dijkstra): when a candidate path of cost `alt` reaches a node whose current
  best cost is `current`, the tentative distance is relaxed to the smaller of
  the two,

      relax current alt = nnrat-min current alt = if (current <= alt)
                                                    then current else alt

  using the decidable rational order. Relaxation is designed to maintain the
  invariant that the relaxed distance is a lower bound of both inputs (relax c a
  <= c and relax c a <= a), and Dijkstra's optimality builds on it; neither is
  proved here in general. The graph, the edge weights, and the visit order are
  executable concerns; what is proved here is the relaxation operation and worked
  instances: relax 7 2 = 2, relax 2 5 = 2, relax 7 2 <= 7, and relax 7 2 <= 2.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all carried by the D63
  checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.path-relaxation`
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))

;; nnrat-min c a = if (c <= a) then c else a
(defn- nnrat-min-term [c a]
  (if-value (decide-at-most c a) c a))

(defn- relax [current alt]
  (function/app (function/const* 'path/relax []) current alt))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; relax current alt = min current alt  (keep the shorter tentative distance)
(def relax-spec
  {:name 'path/relax :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current nnrat] ['alt nnrat]]
                        (nnrat-min-term 'current 'alt))})

(def definition-specs [relax-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A cheaper alternative path (cost 2) relaxes the current best (7) down to 2.
(def relax-improves-spec
  {:name 'path/relax-improves :universes []
   :type (equality nnrat (relax (whole 7) (whole 2)) (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (relax (whole 7) (whole 2)))})

;; No improvement: a costlier alternative (5) leaves the current best (2) intact.
(def relax-keeps-current-spec
  {:name 'path/relax-keeps-current :universes []
   :type (equality nnrat (relax (whole 2) (whole 5)) (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (relax (whole 2) (whole 5)))})

;; Lower bound (1), worked instance: relax 7 2 <= 7.
(def relax-below-current-spec
  {:name 'path/relax-below-current :universes []
   :type (nnrat-at-most (relax (whole 7) (whole 2)) (whole 7))
   :value (at-most-proof (relax (whole 7) (whole 2)) (whole 7))})

;; Lower bound (2), worked instance: relax 7 2 <= 2.
(def relax-below-alt-spec
  {:name 'path/relax-below-alt :universes []
   :type (nnrat-at-most (relax (whole 7) (whole 2)) (whole 2))
   :value (at-most-proof (relax (whole 7) (whole 2)) (whole 2))})

(def theorem-specs
  [relax-improves-spec relax-keeps-current-spec
   relax-below-current-spec relax-below-alt-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :path-relaxation
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
