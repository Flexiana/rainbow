(ns rainbow.algorithms.proofs.ahof.polytope
  "AHoF V34 Polytope Propagation: represent a reachable set as an intersection of
  halfspaces (a polytope) and propagate it forward. A point lies in a two-constraint
  polytope exactly when it satisfies both halfspace inequalities a_i . x <= b_i:

      in-polytope? v1 b1 v2 b2 = (v1 <= b1) AND (v2 <= b2)

  (boolean AND via logic/if-data over the two exact-rational constraint decisions).
  Proved native and axiom-free: the membership conjunction with its unfold, a point
  inside both halfspaces, and a point violating one. Requires audit/decide-nnrat-at-most,
  logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.polytope`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))
(defn- in-polytope? [v1 b1 v2 b2]
  (function/app (function/const* 'polytope/in-polytope? []) v1 b1 v2 b2))

(def in-polytope-spec
  {:name 'polytope/in-polytope? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat bool)
   :value (function/lam [['v1 nnrat] ['b1 nnrat] ['v2 nnrat] ['b2 nnrat]]
                        (and-bool (decide-at-most 'v1 'b1) (decide-at-most 'v2 'b2)))})

(def definition-specs [in-polytope-spec])

(def in-polytope-unfold-spec
  {:name 'polytope/in-polytope-unfold :universes []
   :type (function/forall [['v1 nnrat] ['b1 nnrat] ['v2 nnrat] ['b2 nnrat]]
                          (equality bool (in-polytope? 'v1 'b1 'v2 'b2)
                                    (and-bool (decide-at-most 'v1 'b1)
                                              (decide-at-most 'v2 'b2))))
   :value (function/lam [['v1 nnrat] ['b1 nnrat] ['v2 nnrat] ['b2 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      bool (in-polytope? 'v1 'b1 'v2 'b2)))})

;; A point satisfying both halfspaces (1/2<=3/4, 1/2<=3/4) is inside.
(def inside-both-halfspaces-spec
  {:name 'polytope/inside-both-halfspaces :universes []
   :type (equality bool (in-polytope? (fraction 1 1) (fraction 3 3) (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-polytope? (fraction 1 1) (fraction 3 3) (fraction 1 1) (fraction 3 3)))})

;; A point violating the second halfspace (3/4 > 1/2) is outside.
(def violates-halfspace-outside-spec
  {:name 'polytope/violates-halfspace-outside :universes []
   :type (equality bool (in-polytope? (fraction 1 1) (fraction 3 3) (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-polytope? (fraction 1 1) (fraction 3 3) (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [in-polytope-unfold-spec inside-both-halfspaces-spec violates-halfspace-outside-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-polytope (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.polytope))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
