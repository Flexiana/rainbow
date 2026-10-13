(ns rainbow.algorithms.proofs.ahof.dijkstra
  "AHoF Dijkstra's Shortest Path: single-source shortest paths on a graph with
  NON-NEGATIVE edge weights. Unlike Bellman-Ford (which relaxes all edges V-1
  times), Dijkstra greedily finalizes, at each step, the unvisited vertex with the
  smallest tentative distance -- correct precisely because non-negative weights
  guarantee that vertex's distance can no longer improve. Selecting the closer of
  two frontier vertices is:

      closer-vertex da na db nb = if da <= db then na else nb

  (return the id of the smaller-distance vertex), over exact-rational tentative
  distances. Proved native and axiom-free: the closest-vertex selection; worked
  choices (vertex 2 at 3 against vertex 5 at 8 picks 2; at 4 against 9 it picks
  5); and the certificate 3 <= 8 as a native nnrat/at-most. Correctness of greedy
  finalization under non-negative weights is classical and is not proved here.
  The priority queue and edge relaxation are executable; what is proved is the
  closest-frontier selection at these instances.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.dijkstra`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- closer-vertex [da na db nb]
  (function/app (function/const* 'dijkstra/closer-vertex []) da na db nb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; closer-vertex da na db nb = if da <= db then na else nb
(def closer-vertex-spec
  {:name 'dijkstra/closer-vertex :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['da nnrat] ['na nat] ['db nnrat] ['nb nat]]
                        (if-nat (decide-at-most 'da 'db) 'na 'nb))})

(def definition-specs [closer-vertex-spec])

;; Theorems -----------------------------------------------------------------

;; Vertex 2 at distance 3 is closer than vertex 5 at distance 8: finalize 2.
(def finalizes-closest-spec
  {:name 'dijkstra/finalizes-closest :universes []
   :type (equality nat
                   (closer-vertex (whole 3) (data-nat 2) (whole 8) (data-nat 5))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (closer-vertex (whole 3) (data-nat 2)
                                       (whole 8) (data-nat 5)))})

;; When the second vertex is closer, it is finalized instead.
(def finalizes-second-when-closer-spec
  {:name 'dijkstra/finalizes-second-when-closer :universes []
   :type (equality nat
                   (closer-vertex (whole 9) (data-nat 2) (whole 4) (data-nat 5))
                   (data-nat 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (closer-vertex (whole 9) (data-nat 2)
                                       (whole 4) (data-nat 5)))})

;; Worked certificate: the selected distance 3 is at most the alternative 8.
(def finalized-is-closest-spec
  {:name 'dijkstra/finalized-is-closest :universes []
   :type (nnrat-at-most (whole 3) (whole 8))
   :value (at-most-proof (whole 3) (whole 8))})

(def theorem-specs
  [finalizes-closest-spec finalizes-second-when-closer-spec
   finalized-is-closest-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-dijkstra
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
