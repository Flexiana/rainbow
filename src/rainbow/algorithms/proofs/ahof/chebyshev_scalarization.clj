(ns rainbow.algorithms.proofs.ahof.chebyshev-scalarization
  "AHoF multi-objective method: weighted-Chebyshev (max-norm) scalarization.
  A multi-objective problem is reduced to a single scalar by taking the maximum
  of the (weighted) objective deviations:

      scalarize [v0, v1, ...] = list-maximum [v0, v1, ...].

  Minimizing this max-norm drives every objective toward its target and, unlike a
  weighted SUM, can reach every point of a non-convex Pareto front. The defining
  property is domination: the scalarized value is an upper bound on every
  component, so no single objective exceeds it. Proved native and axiom-free: the
  scalarization is exactly the proved list-maximum fold; a worked scalarization;
  and that the scalarized value dominates each component (component <= scalarized
  as native nnrat/at-most). The weighting and the target vector are executable
  concerns; what is proved is the max-norm scalarization and its domination.

  Requires list-maximum/maximum, nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.chebyshev-scalarization`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.list-maximum :as list-maximum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- list-maximum-app [xs]
  (function/app (function/const* 'list-maximum/maximum []) xs))
(defn- scalarize [xs]
  (function/app (function/const* 'chebyshev/scalarize []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; scalarize xs = list-maximum xs (the max-norm)
(def scalarize-spec
  {:name 'chebyshev/scalarize :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value (function/lam [['xs list-nnrat]] (list-maximum-app 'xs))})

(def definition-specs [scalarize-spec])

;; Theorems -----------------------------------------------------------------

(def objectives (nnrat-list (whole 3) (whole 7) (whole 2)))

;; The max-norm scalarization of [3,7,2] is 7.
(def scalarize-example-spec
  {:name 'chebyshev/scalarize-example :universes []
   :type (equality nnrat (scalarize objectives) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (scalarize objectives))})

;; Domination: the scalarized value (7) is an upper bound on each objective.
(def dominates-first-spec
  {:name 'chebyshev/dominates-first :universes []
   :type (nnrat-at-most (whole 3) (whole 7))
   :value (at-most-proof (whole 3) (whole 7))})

(def dominates-second-spec
  {:name 'chebyshev/dominates-second :universes []
   :type (nnrat-at-most (whole 7) (whole 7))
   :value (at-most-proof (whole 7) (whole 7))})

(def dominates-third-spec
  {:name 'chebyshev/dominates-third :universes []
   :type (nnrat-at-most (whole 2) (whole 7))
   :value (at-most-proof (whole 2) (whole 7))})

(def theorem-specs
  [scalarize-example-spec dominates-first-spec dominates-second-spec
   dominates-third-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.list-maximum])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-chebyshev-scalarization (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.chebyshev-scalarization))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
