(ns rainbow.algorithms.proofs.ahof.articulation-points
  "AHoF Articulation Points (Tarjan's DFS low-link algorithm): find the cut vertices
  of an undirected graph -- those whose removal disconnects it -- in O(V + E), the
  basis of network-reliability and bridge analysis. During DFS, disc[u] is u's
  discovery time and low[v] is the earliest discovery time reachable from v's
  subtree (via tree or one back edge). A non-root vertex u is an articulation point
  when some CHILD v cannot reach any ancestor of u -- i.e. low[v] is no earlier than
  disc[u], so the subtree has no escape route above u:

      is-articulation? disc-u child-low = decide (disc-u <= child-low)

  over exact-rational (integer) DFS timestamps. Proved native and axiom-free: the
  cut-vertex test; that a child whose low-link is at least u's discovery time makes
  u an articulation point; the certificate that in that case u's discovery time is
  at most the child's low-link (native nnrat/at-most) -- the subtree is trapped below
  u; and that a child reaching above u (smaller low-link) does NOT make u a cut
  vertex. The DFS with discovery/low bookkeeping is executable; what is proved is the
  articulation-point decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.articulation-points`
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

(defn- is-articulation? [disc-u child-low]
  (function/app (function/const* 'articulation-points/is-articulation? [])
                disc-u child-low))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; is-articulation? disc-u child-low = decide (disc-u <= child-low)
(def is-articulation-spec
  {:name 'articulation-points/is-articulation? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['disc-u nnrat] ['child-low nnrat]]
                        (decide-at-most 'disc-u 'child-low))})

(def definition-specs [is-articulation-spec])

;; Theorems -----------------------------------------------------------------

;; A child whose low-link (5) is at least u's discovery time (3) traps its subtree
;; below u -> u is an articulation point.
(def trapped-child-articulation-spec
  {:name 'articulation-points/trapped-child-articulation :universes []
   :type (equality bool (is-articulation? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-articulation? (whole 3) (whole 5)))})

;; Certificate: when u is a cut vertex, its discovery time is at most the child's
;; low-link (3 <= 5) -- the subtree cannot escape above u.
(def subtree-trapped-below-spec
  {:name 'articulation-points/subtree-trapped-below :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A child that reaches above u (low-link 1 < disc 3) does NOT make u a cut vertex.
(def escaping-child-not-articulation-spec
  {:name 'articulation-points/escaping-child-not-articulation :universes []
   :type (equality bool (is-articulation? (whole 3) (whole 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-articulation? (whole 3) (whole 1)))})

(def theorem-specs
  [trapped-child-articulation-spec subtree-trapped-below-spec
   escaping-child-not-articulation-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-articulation-points (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.articulation-points))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
