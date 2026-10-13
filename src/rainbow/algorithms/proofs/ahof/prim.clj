(ns rainbow.algorithms.proofs.ahof.prim
  "AHoF Prim's Minimum Spanning Tree: grow an MST from a start vertex by
  repeatedly adding the minimum-weight edge that CROSSES THE CUT between the
  in-tree vertices and the rest. Unlike Kruskal (which sorts all edges globally
  and uses union-find), Prim maintains a frontier of candidate crossing edges and
  greedily takes the lightest. Choosing between two crossing edges by weight is:

      lighter-edge wa ea wb eb = if wa <= wb then ea else eb

  (return the endpoint/id of the lighter crossing edge), over exact-rational edge
  weights. Defined: the two-edge selection. Proved native and axiom-free, as
  worked instances: between weights 1 and 4 the first edge (to vertex 2) is
  chosen, between weights 6 and 3 the second (to vertex 5) is chosen, and the
  worked certificate 1 <= 4 (native nnrat/at-most). The cut property (a
  lightest crossing edge belongs to some MST) and the minimality of the tree
  Prim grows are classical and not proved here. The frontier priority queue and
  cut maintenance are executable.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.prim`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- lighter-edge [wa ea wb eb]
  (function/app (function/const* 'prim/lighter-edge []) wa ea wb eb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; lighter-edge wa ea wb eb = if wa <= wb then ea else eb
(def lighter-edge-spec
  {:name 'prim/lighter-edge :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['wa nnrat] ['ea nat] ['wb nnrat] ['eb nat]]
                        (if-nat (decide-at-most 'wa 'wb) 'ea 'eb))})

(def definition-specs [lighter-edge-spec])

;; Theorems -----------------------------------------------------------------

;; Crossing edge to vertex 2 (weight 1) is lighter than the one to vertex 5
;; (weight 4): grow the tree by adding vertex 2.
(def picks-lighter-crossing-spec
  {:name 'prim/picks-lighter-crossing :universes []
   :type (equality nat
                   (lighter-edge (whole 1) (data-nat 2) (whole 4) (data-nat 5))
                   (data-nat 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (lighter-edge (whole 1) (data-nat 2)
                                      (whole 4) (data-nat 5)))})

;; When the second edge is lighter, that endpoint is added instead.
(def picks-second-when-lighter-spec
  {:name 'prim/picks-second-when-lighter :universes []
   :type (equality nat
                   (lighter-edge (whole 6) (data-nat 2) (whole 3) (data-nat 5))
                   (data-nat 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (lighter-edge (whole 6) (data-nat 2)
                                      (whole 3) (data-nat 5)))})

;; Worked certificate 1 <= 4: the chosen edge's weight is at most the
;; alternative's. The cut property and MST optimality are classical and not
;; proved here.
(def chosen-edge-is-minimum-spec
  {:name 'prim/chosen-edge-is-minimum :universes []
   :type (nnrat-at-most (whole 1) (whole 4))
   :value (at-most-proof (whole 1) (whole 4))})

(def theorem-specs
  [picks-lighter-crossing-spec picks-second-when-lighter-spec
   chosen-edge-is-minimum-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-prim (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.prim))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
