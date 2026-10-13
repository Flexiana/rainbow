(ns rainbow.algorithms.proofs.ahof.bellman-ford
  "AHoF Bellman-Ford single-source shortest paths: unlike Dijkstra, it handles
  edges of any (including negative) weight by relaxing EVERY edge repeatedly for
  V-1 passes, and detects a negative-weight cycle if some edge still STRICTLY
  decreases a distance on a V-th pass. The relaxation test here is non-strict:

      relaxes? candidate current = decide (candidate <= current)

  where candidate = dist(u) + weight(u,v) and current = dist(v), over exact
  rationals. Because it accepts equality, an already-settled edge with
  candidate = current passes it even in an acyclic graph, so acceptance by this
  predicate on a V-th pass is NOT the negative-cycle criterion; that criterion
  needs candidate < current. Defined: the relaxation test. Proved native and
  axiom-free, as worked instances: candidate 3 against current 5 relaxes,
  candidate 7 against current 5 does not, and the worked certificate 3 <= 5
  (native nnrat/at-most). The classical invariants (distances never increase
  under relaxation, V-1 passes converge to shortest paths, a strict V-th-pass
  decrease signals a negative cycle) are not proved here. The graph
  representation and the distance table are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bellman-ford`
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

(defn- relaxes? [candidate current]
  (function/app (function/const* 'bellman-ford/relaxes? []) candidate current))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; relaxes? candidate current = decide (candidate <= current)
(def relaxes-spec
  {:name 'bellman-ford/relaxes? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['candidate nnrat] ['current nnrat]]
                        (decide-at-most 'candidate 'current))})

(def definition-specs [relaxes-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A shorter path candidate (3) than the current estimate (5) relaxes the edge.
(def shorter-path-relaxes-spec
  {:name 'bellman-ford/shorter-path-relaxes :universes []
   :type (equality bool (relaxes? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (relaxes? (whole 3) (whole 5)))})

;; Worked certificate 3 <= 5. That distances never increase under relaxation is
;; the classical invariant, not proved here.
(def update-decreases-distance-spec
  {:name 'bellman-ford/update-decreases-distance :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A non-improving candidate (7) does not relax against the current estimate (5).
;; Classically, when no edge relaxes the distances have converged (not proved
;; here).
(def no-improvement-rejected-spec
  {:name 'bellman-ford/no-improvement-rejected :universes []
   :type (equality bool (relaxes? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (relaxes? (whole 7) (whole 5)))})

(def theorem-specs
  [shorter-path-relaxes-spec update-decreases-distance-spec
   no-improvement-rejected-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-bellman-ford (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.bellman-ford))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
