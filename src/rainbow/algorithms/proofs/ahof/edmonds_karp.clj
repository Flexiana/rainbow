(ns rainbow.algorithms.proofs.ahof.edmonds-karp
  "AHoF Edmonds-Karp Algorithm: compute the maximum flow through a network in
  O(V*E^2) by repeatedly finding a SHORTEST augmenting path (by BFS) in the
  residual graph and pushing flow along it, until none remains -- a concrete
  polynomial realization of Ford-Fulkerson. The BFS may traverse an edge only while
  it has RESIDUAL CAPACITY (its current flow is below its capacity, i.e. residual =
  capacity - flow > 0):

      has-residual? residual = decide (1 <= residual)

  over exact-rational (integer) residual capacities. Proved native and axiom-free:
  the residual test; that an edge with positive residual can carry more flow (it is
  part of the residual graph the BFS explores); the certificate that a usable
  edge's residual is at least one unit (native nnrat/at-most); and that a saturated
  edge (zero residual) is unusable. The BFS, augmentation, and residual bookkeeping
  are executable; what is proved is the residual-capacity decision, whose repetition
  yields the max flow (equal to the min cut).

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.edmonds-karp`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- has-residual? [residual]
  (function/app (function/const* 'edmonds-karp/has-residual? []) residual))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; has-residual? residual = decide (1 <= residual)
(def has-residual-spec
  {:name 'edmonds-karp/has-residual? :kind :definition :universes []
   :type (function/arrow nnrat bool)
   :value (function/lam [['residual nnrat]]
                        (decide-at-most (whole 1) 'residual))})

(def definition-specs [has-residual-spec])

;; Theorems -----------------------------------------------------------------

;; An edge with residual capacity 3 can carry more flow (usable in the BFS).
(def positive-residual-usable-spec
  {:name 'edmonds-karp/positive-residual-usable :universes []
   :type (equality bool (has-residual? (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (has-residual? (whole 3)))})

;; Certificate: a usable edge's residual is at least one unit (1 <= 3).
(def usable-residual-at-least-one-spec
  {:name 'edmonds-karp/usable-residual-at-least-one :universes []
   :type (nnrat-at-most (whole 1) (whole 3))
   :value (at-most-proof (whole 1) (whole 3))})

;; A saturated edge (residual 0) is unusable -- the BFS cannot traverse it.
(def saturated-edge-unusable-spec
  {:name 'edmonds-karp/saturated-edge-unusable :universes []
   :type (equality bool (has-residual? (whole 0))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (has-residual? (whole 0)))})

(def theorem-specs
  [positive-residual-usable-spec usable-residual-at-least-one-spec
   saturated-edge-unusable-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-edmonds-karp (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.edmonds-karp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
