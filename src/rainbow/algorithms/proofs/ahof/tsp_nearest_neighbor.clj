(ns rainbow.algorithms.proofs.ahof.tsp-nearest-neighbor
  "AHoF Nearest-Neighbor TSP heuristic: build a tour of the Travelling Salesman
  Problem by starting at a city and repeatedly travelling to the NEAREST unvisited
  city, returning to the start at the end. It is a fast constructive heuristic
  (not optimal, but a common baseline and warm-start for local search). At each
  step it selects the closer of two candidate unvisited cities:

      nearer-city da na db nb = if da <= db then na else nb

  (return the id of the smaller-distance city), over exact-rational distances.
  Proved native and axiom-free: the nearest-city selection; a worked choice of the
  nearer city; and the certificate that the visited city's distance is at most the
  alternative's (native nnrat/at-most) -- a worked instance of the greedy
  nearest-neighbor invariant, not a proof of it for all distances.
  The distance matrix and the visited-set bookkeeping are executable; what is
  proved is the nearest-unvisited-city selection.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.tsp-nearest-neighbor`
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

(defn- nearer-city [da na db nb]
  (function/app (function/const* 'tsp-nn/nearer-city []) da na db nb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; nearer-city da na db nb = if da <= db then na else nb
(def nearer-city-spec
  {:name 'tsp-nn/nearer-city :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['da nnrat] ['na nat] ['db nnrat] ['nb nat]]
                        (if-nat (decide-at-most 'da 'db) 'na 'nb))})

(def definition-specs [nearer-city-spec])

;; Theorems -----------------------------------------------------------------

;; City 2 at distance 3 is nearer than city 5 at distance 8: travel to city 2.
(def visits-nearest-spec
  {:name 'tsp-nn/visits-nearest :universes []
   :type (equality nat
                   (nearer-city (whole 3) (data-nat 2) (whole 8) (data-nat 5))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (nearer-city (whole 3) (data-nat 2)
                                     (whole 8) (data-nat 5)))})

;; When the second city is nearer, it is visited instead.
(def visits-second-when-nearer-spec
  {:name 'tsp-nn/visits-second-when-nearer :universes []
   :type (equality nat
                   (nearer-city (whole 9) (data-nat 2) (whole 4) (data-nat 5))
                   (data-nat 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (nearer-city (whole 9) (data-nat 2)
                                     (whole 4) (data-nat 5)))})

;; Greedy invariant, worked instance: the visited city's distance is at most the
;; alternative's (3 <= 8).
(def visited-is-nearest-spec
  {:name 'tsp-nn/visited-is-nearest :universes []
   :type (nnrat-at-most (whole 3) (whole 8))
   :value (at-most-proof (whole 3) (whole 8))})

(def theorem-specs
  [visits-nearest-spec visits-second-when-nearer-spec visited-is-nearest-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-tsp-nearest-neighbor
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
