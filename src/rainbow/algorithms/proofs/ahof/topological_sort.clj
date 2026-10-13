(ns rainbow.algorithms.proofs.ahof.topological-sort
  "AHoF Topological Sort (Kahn's algorithm): order the vertices of a DAG so every
  edge points forward -- the canonical dependency/scheduling order. Kahn's method
  repeatedly emits a vertex whose in-degree has dropped to zero (all its
  prerequisites are done) and decrements its successors' in-degrees. A vertex is
  ready to be emitted exactly when its remaining in-degree is zero:

      ready? in-degree = decide (in-degree <= 0)

  over exact-rational in-degree counts (in-degree 0 <= 0 iff it is exactly 0).
  Proved native and axiom-free: the readiness test; that a vertex with no
  remaining prerequisites is ready; that a vertex with outstanding prerequisites
  is not ready; and the certificate that a ready vertex's in-degree is at most
  zero, hence exactly zero (native nnrat/at-most). The adjacency structure and the
  in-degree decrements are executable; what is proved is the readiness decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.topological-sort`
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

(defn- ready? [in-degree]
  (function/app (function/const* 'topological-sort/ready? []) in-degree))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; ready? in-degree = decide (in-degree <= 0)
(def ready-spec
  {:name 'topological-sort/ready? :kind :definition :universes []
   :type (function/arrow nnrat bool)
   :value (function/lam [['in-degree nnrat]]
                        (decide-at-most 'in-degree (whole 0)))})

(def definition-specs [ready-spec])

;; Theorems -----------------------------------------------------------------

;; A vertex whose prerequisites are all satisfied (in-degree 0) is ready.
(def no-prerequisites-ready-spec
  {:name 'topological-sort/no-prerequisites-ready :universes []
   :type (equality bool (ready? (whole 0)) (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (ready? (whole 0)))})

;; A vertex with outstanding prerequisites (in-degree 2) is not yet ready.
(def has-prerequisites-not-ready-spec
  {:name 'topological-sort/has-prerequisites-not-ready :universes []
   :type (equality bool (ready? (whole 2)) (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (ready? (whole 2)))})

;; Certificate: a ready vertex's in-degree is at most zero, hence exactly zero.
(def ready-in-degree-zero-spec
  {:name 'topological-sort/ready-in-degree-zero :universes []
   :type (nnrat-at-most (whole 0) (whole 0))
   :value (at-most-proof (whole 0) (whole 0))})

(def theorem-specs
  [no-prerequisites-ready-spec has-prerequisites-not-ready-spec
   ready-in-degree-zero-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-topological-sort (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.topological-sort))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
