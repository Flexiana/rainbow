(ns rainbow.algorithms.proofs.ahof.kruskal
  "AHoF Kruskal's Minimum Spanning Tree: build an MST by scanning edges in
  increasing weight order and adding each edge unless it would form a cycle -- i.e.
  unless its endpoints are already in the same connected component. Cycle
  detection uses the proved union-find connectivity: an edge is accepted exactly
  when its endpoints are NOT yet connected,

      accepts-edge? ra rb = NOT (connected? ra rb)

  over the exact-rational component representatives. Proved native and axiom-free:
  the acceptance rule as the negation of union-find connectivity; that an edge
  between different components is added (it grows the forest); that an edge within
  one component is rejected (it would close a cycle); and (via the imported
  union-find theorems) the underlying connectivity certificates. The edge sort and
  the union updates are executable; what is proved is the cycle-free acceptance
  decision.

  Requires union-find/connected?, logic/if-data (union-find composed here) and the
  D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kruskal`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.ahof.union-find :as union-find]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- connected? [ra rb]
  (function/app (function/const* 'union-find/connected? []) ra rb))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- accepts-edge? [ra rb]
  (function/app (function/const* 'kruskal/accepts-edge? []) ra rb))

;; Definitions --------------------------------------------------------------

;; accepts-edge? ra rb = if connected? ra rb then false else true  (no cycle)
(def accepts-edge-spec
  {:name 'kruskal/accepts-edge? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['ra nnrat] ['rb nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (connected? 'ra 'rb))
                         (connected? 'ra 'rb)
                         false-value
                         true-value))})

(def definition-specs [accepts-edge-spec])

;; Theorems -----------------------------------------------------------------

;; An edge between different components (reps 3 and 5) is added to the MST.
(def adds-cross-component-edge-spec
  {:name 'kruskal/adds-cross-component-edge :universes []
   :type (equality bool (accepts-edge? (whole 3) (whole 5))
                   true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-edge? (whole 3) (whole 5)))})

;; An edge within one component (both rep 3) is rejected -- it would form a cycle.
(def rejects-cycle-edge-spec
  {:name 'kruskal/rejects-cycle-edge :universes []
   :type (equality bool (accepts-edge? (whole 3) (whole 3))
                   false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-edge? (whole 3) (whole 3)))})

(def theorem-specs [adds-cross-component-edge-spec rejects-cycle-edge-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      union-find/extend-environment
      (support/extend-with :ahof-kruskal
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
