(ns rainbow.algorithms.proofs.ahof.subset-sum
  "AHoF Subset Sum (dynamic programming): decide whether some subset of a set of
  positive integers sums to a target -- the canonical (weakly) NP-complete decision
  problem and the kernel of the partition problem and 0/1-knapsack feasibility. The
  DP fills a boolean table reachable[i][s] = 'some subset of the first i items sums
  to s', and each cell is the OR of two branches: EXCLUDE item i (reachable without
  it) or INCLUDE it (target s - value[i] reachable with the earlier items):

      reachable? include-branch? exclude-branch? = include-branch? OR exclude-branch?

  over booleans. Proved native and axiom-free: the reachability cell as the boolean
  DISJUNCTION of the include and exclude branches (via logic/if-data over Bool --
  the complement of the conjunctions used elsewhere); that either branch being
  reachable makes the sum reachable; and that a sum is unreachable only when BOTH
  branches fail. The value iteration over items and sums is executable; what is
  proved is the reachability OR cell.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.subset-sum`
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

(defn- reachable? [include-branch? exclude-branch?]
  (function/app (function/const* 'subset-sum/reachable? []) include-branch? exclude-branch?))

;; Definitions --------------------------------------------------------------

;; reachable? include exclude = if include then true else exclude   (OR)
(def reachable-spec
  {:name 'subset-sum/reachable? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['include-branch? bool] ['exclude-branch? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'include-branch?) 'include-branch?
                         true-value 'exclude-branch?))})

(def definition-specs [reachable-spec])

;; Theorems -----------------------------------------------------------------

;; Including the item reaches the sum -> the sum is reachable (regardless of the
;; exclude branch).
(def include-branch-reachable-spec
  {:name 'subset-sum/include-branch-reachable :universes []
   :type (equality bool (reachable? true-value false-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (reachable? true-value false-value))})

;; Excluding the item reaches the sum -> the sum is reachable (even if including
;; it does not).
(def exclude-branch-reachable-spec
  {:name 'subset-sum/exclude-branch-reachable :universes []
   :type (equality bool (reachable? false-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (reachable? false-value true-value))})

;; The sum is unreachable only when BOTH branches fail.
(def both-fail-unreachable-spec
  {:name 'subset-sum/both-fail-unreachable :universes []
   :type (equality bool (reachable? false-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (reachable? false-value false-value))})

(def theorem-specs
  [include-branch-reachable-spec exclude-branch-reachable-spec
   both-fail-unreachable-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-subset-sum
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
