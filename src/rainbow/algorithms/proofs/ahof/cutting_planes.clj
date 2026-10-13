(ns rainbow.algorithms.proofs.ahof.cutting-planes
  "AHoF O73 Cutting Planes: solve an integer/convex program by iteratively adding
  linear inequalities (cuts) that remove the current fractional/infeasible LP solution
  while preserving all true solutions. The current point is feasible for a constraint
  a.x <= b when its left-hand side stays within the bound; a cut is added exactly when
  it does not:

      feasible? lhs bound = decide (lhs <= bound)
      add-cut?  lhs bound = NOT (feasible? lhs bound)   (boolean negation via if-data)

  over exact rationals. Proved native and axiom-free: the feasibility decision, the
  add-cut complement, a satisfied point (no cut) and a violated point (cut added).
  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cutting-planes`
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
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- feasible? [lhs bound]
  (function/app (function/const* 'cutting-planes/feasible? []) lhs bound))
(defn- add-cut? [lhs bound]
  (function/app (function/const* 'cutting-planes/add-cut? []) lhs bound))

(def feasible-spec
  {:name 'cutting-planes/feasible? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['lhs nnrat] ['bound nnrat]] (decide-at-most 'lhs 'bound))})

;; add-cut? lhs bound = NOT (feasible? lhs bound)
(def add-cut-spec
  {:name 'cutting-planes/add-cut? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['lhs nnrat] ['bound nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      bool (condition (feasible? 'lhs 'bound))
                                      (feasible? 'lhs 'bound) false-value true-value))})

(def definition-specs [feasible-spec add-cut-spec])

;; A point with lhs 1/2 within bound 3/4 is feasible: no cut.
(def satisfied-no-cut-spec
  {:name 'cutting-planes/satisfied-no-cut :universes []
   :type (equality bool (add-cut? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (add-cut? (fraction 1 1) (fraction 3 3)))})

;; The same point is feasible.
(def point-feasible-spec
  {:name 'cutting-planes/point-feasible :universes []
   :type (equality bool (feasible? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (feasible? (fraction 1 1) (fraction 3 3)))})

;; A point with lhs 3/4 exceeding bound 1/2 is infeasible: a cut is added.
(def violated-cut-added-spec
  {:name 'cutting-planes/violated-cut-added :universes []
   :type (equality bool (add-cut? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (add-cut? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [satisfied-no-cut-spec point-feasible-spec violated-cut-added-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-cutting-planes (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.cutting-planes))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
