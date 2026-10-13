(ns rainbow.algorithms.proofs.ahof.held-karp
  "AHoF Held-Karp Algorithm: solve the Travelling Salesman Problem EXACTLY in
  O(2^n * n^2) -- exponential, but far better than the O(n!) brute force -- by
  dynamic programming over SUBSETS of visited cities. dp[S][j] is the shortest path
  that starts at the origin, visits exactly the cities in S, and ends at j; it
  extends a shorter subpath ending at some predecessor k by the edge k -> j, taking
  the minimum over predecessors:

      path-cost subpath edge = subpath + edge
      better current-best candidate = min(current-best, candidate)
        (if candidate <= current-best then candidate else current-best)

  over exact-rational costs. Defined: the path-cost sum and the min-selection
  between two candidate predecessors. Proved native and axiom-free, as worked
  instances: path-cost 3 4 = 7, better 9 6 = 6, and the worked certificate
  6 <= 9 (native nnrat/at-most). The optimal-substructure property and the
  exactness of Held-Karp for TSP are classical and not proved here. The subset
  enumeration (bitmask DP) is executable.

  Requires nnrat/add, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.held-karp`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- path-cost [subpath edge]
  (function/app (function/const* 'held-karp/path-cost []) subpath edge))
(defn- better [current-best candidate]
  (function/app (function/const* 'held-karp/better []) current-best candidate))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; path-cost subpath edge = subpath + edge
(def path-cost-spec
  {:name 'held-karp/path-cost :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['subpath nnrat] ['edge nnrat]]
                        (nnrat-add 'subpath 'edge))})

;; better current-best candidate = min(current-best, candidate)
(def better-spec
  {:name 'held-karp/better :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current-best nnrat] ['candidate nnrat]]
                        (if-nnrat (decide-at-most 'candidate 'current-best)
                                  'candidate 'current-best))})

(def definition-specs [path-cost-spec better-spec])

;; Theorems -----------------------------------------------------------------

;; Extending a subpath of cost 3 by an edge of cost 4 costs 7.
(def path-cost-example-spec
  {:name 'held-karp/path-cost-example :universes []
   :type (equality nnrat (path-cost (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (path-cost (whole 3) (whole 4)))})

;; The cheaper predecessor (cost 6) beats the current best (9): the cell is 6.
(def takes-cheaper-predecessor-spec
  {:name 'held-karp/takes-cheaper-predecessor :universes []
   :type (equality nnrat (better (whole 9) (whole 6)) (whole 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (better (whole 9) (whole 6)))})

;; Worked certificate 6 <= 9.
(def chosen-subpath-minimal-spec
  {:name 'held-karp/chosen-subpath-minimal :universes []
   :type (nnrat-at-most (whole 6) (whole 9))
   :value (at-most-proof (whole 6) (whole 9))})

(def theorem-specs
  [path-cost-example-spec takes-cheaper-predecessor-spec
   chosen-subpath-minimal-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-held-karp (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.held-karp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
