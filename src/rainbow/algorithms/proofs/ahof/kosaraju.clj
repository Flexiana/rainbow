(ns rainbow.algorithms.proofs.ahof.kosaraju
  "AHoF Kosaraju's Algorithm: find the strongly connected components (SCCs) of a
  directed graph in O(V + E) via two depth-first passes -- one on the graph
  (recording finish order) and one on the TRANSPOSE (grouping by reachability in
  decreasing finish order). Two vertices lie in the same SCC exactly when each is
  reachable from the other:

      same-scc? u-reaches-v? v-reaches-u? = u-reaches-v? AND v-reaches-u?

  over booleans. Proved native and axiom-free: the same-component test as the
  boolean conjunction of the two directed reachabilities (via logic/if-data over
  Bool); that mutual reachability puts two vertices in one SCC; and that if EITHER
  direction is unreachable they are in different SCCs. The two DFS passes and the
  component labelling are executable; what is proved is the mutual-reachability SCC
  membership decision (the condensation of the graph is a DAG of these components).

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kosaraju`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- same-scc? [u-reaches-v? v-reaches-u?]
  (function/app (function/const* 'kosaraju/same-scc? []) u-reaches-v? v-reaches-u?))

;; Definitions --------------------------------------------------------------

;; same-scc? u->v v->u = if u->v then v->u else false   (mutual reachability, AND)
(def same-scc-spec
  {:name 'kosaraju/same-scc? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['u-reaches-v? bool] ['v-reaches-u? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'u-reaches-v?) 'u-reaches-v?
                         'v-reaches-u? false-value))})

(def definition-specs [same-scc-spec])

;; Theorems -----------------------------------------------------------------

;; Mutual reachability (u->v and v->u) puts two vertices in the same SCC.
(def mutual-reach-same-scc-spec
  {:name 'kosaraju/mutual-reach-same-scc :universes []
   :type (equality bool (same-scc? true-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (same-scc? true-value true-value))})

;; If v is not reachable from u, they are in different SCCs.
(def forward-unreachable-different-spec
  {:name 'kosaraju/forward-unreachable-different :universes []
   :type (equality bool (same-scc? false-value true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (same-scc? false-value true-value))})

;; If u is not reachable from v, they are in different SCCs.
(def backward-unreachable-different-spec
  {:name 'kosaraju/backward-unreachable-different :universes []
   :type (equality bool (same-scc? true-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (same-scc? true-value false-value))})

(def theorem-specs
  [mutual-reach-same-scc-spec forward-unreachable-different-spec
   backward-unreachable-different-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-kosaraju (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.kosaraju))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
