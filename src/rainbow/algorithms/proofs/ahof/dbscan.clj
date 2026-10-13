(ns rainbow.algorithms.proofs.ahof.dbscan
  "AHoF DBSCAN (Density-Based Spatial Clustering of Applications with Noise): find
  clusters of arbitrary shape as dense regions separated by sparse ones, labelling
  low-density points as noise -- without needing the number of clusters in advance.
  The engine is the CORE-POINT test: a point is a core point (the seed of a
  cluster) when its epsilon-neighborhood contains at least minPts points:

      is-core? neighbor-count min-pts = decide (min-pts <= neighbor-count)

  over exact-rational (integer) counts. Proved native and axiom-free: the
  core-point test; that a point in a dense region is a core point; the certificate
  that a core point really has at least minPts neighbors (native nnrat/at-most) --
  the density criterion; and that a sparse point is not a core point (it is a
  border or noise point). The region queries and cluster expansion are executable;
  what is proved is the density core-point decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.dbscan`
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

(defn- is-core? [neighbor-count min-pts]
  (function/app (function/const* 'dbscan/is-core? []) neighbor-count min-pts))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; is-core? neighbor-count min-pts = decide (min-pts <= neighbor-count)
(def is-core-spec
  {:name 'dbscan/is-core? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['neighbor-count nnrat] ['min-pts nnrat]]
                        (decide-at-most 'min-pts 'neighbor-count))})

(def definition-specs [is-core-spec])

;; Theorems -----------------------------------------------------------------

;; A point with 5 neighbors, min-pts 3, is a core point (dense region).
(def dense-point-is-core-spec
  {:name 'dbscan/dense-point-is-core :universes []
   :type (equality bool (is-core? (whole 5) (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-core? (whole 5) (whole 3)))})

;; Density certificate: a core point has at least min-pts neighbors (3 <= 5).
(def core-meets-density-spec
  {:name 'dbscan/core-meets-density :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A point with only 2 neighbors (min-pts 3) is not a core point (border/noise).
(def sparse-point-not-core-spec
  {:name 'dbscan/sparse-point-not-core :universes []
   :type (equality bool (is-core? (whole 2) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-core? (whole 2) (whole 3)))})

(def theorem-specs
  [dense-point-is-core-spec core-meets-density-spec sparse-point-not-core-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-dbscan (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.dbscan))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
