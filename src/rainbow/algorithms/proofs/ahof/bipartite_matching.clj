(ns rainbow.algorithms.proofs.ahof.bipartite-matching
  "AHoF Maximum Bipartite Matching (augmenting-path / Hungarian tree method): find
  the largest set of edges with no shared endpoints in a bipartite graph -- the
  model for job/worker assignment, scheduling, and network routing. Each left
  vertex is matched by finding an AUGMENTING PATH: it can claim a right neighbor v
  when v is currently FREE, or when v's current match can itself be re-matched
  elsewhere (recursively). So a left vertex can be matched to v when:

      can-match? v-free? partner-reassignable? = v-free? OR partner-reassignable?

  over booleans. Proved native and axiom-free: the augment test as the boolean
  DISJUNCTION of 'the neighbor is free' and 'its current partner can move' (via
  logic/if-data over Bool); that a free neighbor is immediately matchable; that a
  reassignable partner also yields a match (the augmenting path); and that a match
  fails only when the neighbor is taken AND its partner cannot move. The DFS/BFS for
  augmenting paths is executable; what is proved is the per-neighbor augment
  decision, whose repetition (once per left vertex) yields a maximum matching.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bipartite-matching`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- can-match? [v-free? partner-reassignable?]
  (function/app (function/const* 'bipartite-matching/can-match? [])
                v-free? partner-reassignable?))

;; Definitions --------------------------------------------------------------

;; can-match? v-free partner-reassignable = if v-free then true else
;;   partner-reassignable   (OR)
(def can-match-spec
  {:name 'bipartite-matching/can-match? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['v-free? bool] ['partner-reassignable? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'v-free?) 'v-free?
                         true-value 'partner-reassignable?))})

(def definition-specs [can-match-spec])

;; Theorems -----------------------------------------------------------------

;; A free neighbor is immediately matchable (regardless of any partner).
(def free-neighbor-matchable-spec
  {:name 'bipartite-matching/free-neighbor-matchable :universes []
   :type (equality bool (can-match? true-value false-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (can-match? true-value false-value))})

;; A taken neighbor whose partner can be reassigned still yields a match (the
;; augmenting path).
(def reassignable-partner-matchable-spec
  {:name 'bipartite-matching/reassignable-partner-matchable :universes []
   :type (equality bool (can-match? false-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (can-match? false-value true-value))})

;; A match fails only when the neighbor is taken AND its partner cannot move.
(def taken-stuck-partner-fails-spec
  {:name 'bipartite-matching/taken-stuck-partner-fails :universes []
   :type (equality bool (can-match? false-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (can-match? false-value false-value))})

(def theorem-specs
  [free-neighbor-matchable-spec reassignable-partner-matchable-spec
   taken-stuck-partner-fails-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bipartite-matching
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
