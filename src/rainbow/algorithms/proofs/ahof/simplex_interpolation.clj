(ns rainbow.algorithms.proofs.ahof.simplex-interpolation
  "AHoF D28 Simplex Interpolation: interpolate a value function over a simplicial
  grid using barycentric coordinates. A query point inside a simplex is a convex
  combination of the simplex vertices with barycentric weights lambda_i summing
  to one; the interpolated value is the same convex combination of the vertex
  values:

      interpolate l1 v1 l2 v2 l3 v3 = l1*v1 + l2*v2 + l3*v3

  over exact nonnegative rationals (a 2-simplex / triangle; a d-simplex folds over
  d+1 vertices). Proved native and axiom-free: the barycentric combination and
  worked instances that reduce by reflexivity. The simplex location (which
  simplex contains the query) and the barycentric-coordinate solve are executable
  concerns; the weights and vertex values are supplied rationals. What is proved
  here is the deterministic interpolation arithmetic.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.simplex-interpolation`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- interpolate [l1 v1 l2 v2 l3 v3]
  (function/app (function/const* 'simplex-interpolation/interpolate [])
                l1 v1 l2 v2 l3 v3))

;; Definitions --------------------------------------------------------------

;; interpolate l1 v1 l2 v2 l3 v3 = l1*v1 + l2*v2 + l3*v3
(def interpolate-spec
  {:name 'simplex-interpolation/interpolate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['l1 nnrat] ['v1 nnrat] ['l2 nnrat] ['v2 nnrat]
                         ['l3 nnrat] ['v3 nnrat]]
                        (nnrat-add
                         (nnrat-add (nnrat-multiply 'l1 'v1)
                                    (nnrat-multiply 'l2 'v2))
                         (nnrat-multiply 'l3 'v3)))})

(def definition-specs [interpolate-spec])

;; Theorems -----------------------------------------------------------------

(def interpolate-unfold-spec
  {:name 'simplex-interpolation/interpolate-unfold :universes []
   :type (function/forall
          [['l1 nnrat] ['v1 nnrat] ['l2 nnrat] ['v2 nnrat]
           ['l3 nnrat] ['v3 nnrat]]
          (equality nnrat
                    (interpolate 'l1 'v1 'l2 'v2 'l3 'v3)
                    (nnrat-add
                     (nnrat-add (nnrat-multiply 'l1 'v1)
                                (nnrat-multiply 'l2 'v2))
                     (nnrat-multiply 'l3 'v3))))
   :value (function/lam [['l1 nnrat] ['v1 nnrat] ['l2 nnrat] ['v2 nnrat]
                         ['l3 nnrat] ['v3 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (interpolate 'l1 'v1 'l2 'v2 'l3 'v3)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked interpolation: weights (2,1,3), vertex values (3,4,1) ->
;; 2*3 + 1*4 + 3*1 = 13.
(def interpolate-example-spec
  {:name 'simplex-interpolation/interpolate-example :universes []
   :type (equality nnrat
                   (interpolate (whole 2) (whole 3) (whole 1) (whole 4)
                                (whole 3) (whole 1))
                   (whole 13))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (interpolate (whole 2) (whole 3) (whole 1) (whole 4)
                                     (whole 3) (whole 1)))})

;; A query at a vertex (weights (1,0,0)) returns that vertex's value: -> 3.
(def interpolate-at-vertex-spec
  {:name 'simplex-interpolation/interpolate-at-vertex :universes []
   :type (equality nnrat
                   (interpolate (whole 1) (whole 3) (whole 0) (whole 4)
                                (whole 0) (whole 1))
                   (whole 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (interpolate (whole 1) (whole 3) (whole 0) (whole 4)
                                     (whole 0) (whole 1)))})

(def theorem-specs
  [interpolate-unfold-spec interpolate-example-spec interpolate-at-vertex-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-simplex-interpolation (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.simplex-interpolation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
