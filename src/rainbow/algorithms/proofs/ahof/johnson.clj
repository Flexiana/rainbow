(ns rainbow.algorithms.proofs.ahof.johnson
  "AHoF Johnson's Algorithm (all-pairs shortest paths): compute shortest paths
  between EVERY pair of vertices in a sparse, possibly negative-weight (but
  cycle-free) graph in O(V*E + V^2 log V) -- faster than Floyd-Warshall on sparse
  graphs. It adds a virtual source, runs Bellman-Ford to get a potential h(v) at
  each vertex, then REWEIGHTS every edge to w'(u,v) = w(u,v) + h(u) - h(v), which is
  provably non-negative, so Dijkstra can be run from each vertex. The key invariant
  the reweighting establishes is edge non-negativity:

      nonneg-reweighted? reweighted-weight = decide (0 <= reweighted-weight)

  over exact-rational reweighted edge weights. Proved native and axiom-free: the
  non-negativity test, and worked instances -- a reweighted weight of 4 passes;
  the certificate 0 <= 4 as a native nnrat/at-most; and a tight edge of weight 0
  passes. That the potential h makes every reweighted edge non-negative is the
  classical invariant and is not proved here. The Bellman-Ford potential pass,
  the reweighting, and per-source Dijkstra are executable; what is proved is the
  reweighted-non-negativity decision at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.johnson`
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

(defn- nonneg-reweighted? [reweighted-weight]
  (function/app (function/const* 'johnson/nonneg-reweighted? []) reweighted-weight))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; nonneg-reweighted? reweighted-weight = decide (0 <= reweighted-weight)
(def nonneg-reweighted-spec
  {:name 'johnson/nonneg-reweighted? :kind :definition :universes []
   :type (function/arrow nnrat bool)
   :value (function/lam [['reweighted-weight nnrat]]
                        (decide-at-most (whole 0) 'reweighted-weight))})

(def definition-specs [nonneg-reweighted-spec])

;; Theorems -----------------------------------------------------------------

;; A reweighted edge weight of 4 is non-negative -- Dijkstra can use it.
(def reweighted-edge-nonneg-spec
  {:name 'johnson/reweighted-edge-nonneg :universes []
   :type (equality bool (nonneg-reweighted? (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (nonneg-reweighted? (whole 4)))})

;; Certificate for the worked edge: 0 <= 4.
(def valid-reweight-at-least-zero-spec
  {:name 'johnson/valid-reweight-at-least-zero :universes []
   :type (nnrat-at-most (whole 0) (whole 4))
   :value (at-most-proof (whole 0) (whole 4))})

;; A reweighted weight of exactly zero (a tight edge) is still non-negative and
;; usable.
(def zero-reweight-usable-spec
  {:name 'johnson/zero-reweight-usable :universes []
   :type (equality bool (nonneg-reweighted? (whole 0))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (nonneg-reweighted? (whole 0)))})

(def theorem-specs
  [reweighted-edge-nonneg-spec valid-reweight-at-least-zero-spec
   zero-reweight-usable-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-johnson
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
