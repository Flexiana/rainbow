(ns rainbow.algorithms.proofs.ahof.tabu-search
  "AHoF Tabu Search: a local-search metaheuristic that escapes local optima by
  ALWAYS moving to the best neighbor -- even a worsening one -- while a short-term
  memory (the TABU LIST) forbids reversing recent moves, preventing cycling. A
  candidate move is allowed exactly when it is NOT currently tabu:

      move-allowed? move-is-tabu? = NOT move-is-tabu?

  over booleans. Proved native and axiom-free: the allowed-move test as the boolean
  negation of the tabu status (via logic/if-data over Bool); that a non-tabu move is
  allowed; and that a tabu move is forbidden -- unless it would improve on the best
  solution ever seen (the aspiration criterion, an override handled by the caller).
  The neighborhood evaluation, tabu-list tenure, and best-so-far tracking are
  executable; what is proved is the tabu-membership move decision.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.tabu-search`
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

(defn- move-allowed? [move-is-tabu?]
  (function/app (function/const* 'tabu-search/move-allowed? []) move-is-tabu?))

;; Definitions --------------------------------------------------------------

;; move-allowed? move-is-tabu? = if move-is-tabu? then false else true   (NOT)
(def move-allowed-spec
  {:name 'tabu-search/move-allowed? :kind :definition :universes []
   :type (function/arrow bool bool)
   :value (function/lam
           [['move-is-tabu? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'move-is-tabu?) 'move-is-tabu?
                         false-value true-value))})

(def definition-specs [move-allowed-spec])

;; Theorems -----------------------------------------------------------------

;; A move that is not on the tabu list is allowed.
(def non-tabu-move-allowed-spec
  {:name 'tabu-search/non-tabu-move-allowed :universes []
   :type (equality bool (move-allowed? false-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (move-allowed? false-value))})

;; A move on the tabu list is forbidden (blocks cycling back).
(def tabu-move-forbidden-spec
  {:name 'tabu-search/tabu-move-forbidden :universes []
   :type (equality bool (move-allowed? true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (move-allowed? true-value))})

(def theorem-specs [non-tabu-move-allowed-spec tabu-move-forbidden-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-tabu-search
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
