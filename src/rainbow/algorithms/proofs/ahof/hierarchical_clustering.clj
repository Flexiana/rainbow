(ns rainbow.algorithms.proofs.ahof.hierarchical-clustering
  "AHoF Agglomerative Hierarchical Clustering: build a hierarchy of clusters
  (a dendrogram) bottom-up -- start with each point in its own cluster and
  repeatedly MERGE THE TWO CLOSEST clusters, under a linkage that defines
  inter-cluster distance (single / complete / average). Unlike k-means it needs no
  preset k and yields a full tree that can be cut at any level. At each step it
  selects the closest of two candidate cluster pairs by linkage distance:

      closest-pair dab pab dcd pcd = if dab <= dcd then pab else pcd

  (return the id of the smaller-distance pair), over exact-rational distances.
  Proved native and axiom-free: the closest-pair selection; a worked choice of the
  nearer pair; and the certificate that the merged pair's distance is at most the
  alternative's (native nnrat/at-most) -- the greedy merge that shapes the
  dendrogram. The linkage distances and the merge bookkeeping are executable; what
  is proved is the closest-pair merge decision.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hierarchical-clustering`
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

(defn- closest-pair [dab pab dcd pcd]
  (function/app (function/const* 'hierarchical/closest-pair []) dab pab dcd pcd))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; closest-pair dab pab dcd pcd = if dab <= dcd then pab else pcd
(def closest-pair-spec
  {:name 'hierarchical/closest-pair :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['dab nnrat] ['pab nat] ['dcd nnrat] ['pcd nat]]
                        (if-nat (decide-at-most 'dab 'dcd) 'pab 'pcd))})

(def definition-specs [closest-pair-spec])

;; Theorems -----------------------------------------------------------------

;; Pair 0 at distance 2 is closer than pair 1 at distance 6: merge pair 0.
(def merges-closest-pair-spec
  {:name 'hierarchical/merges-closest-pair :universes []
   :type (equality nat
                   (closest-pair (whole 2) (data-nat 0) (whole 6) (data-nat 1))
                   (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (closest-pair (whole 2) (data-nat 0)
                                      (whole 6) (data-nat 1)))})

;; When the second pair is closer, it is merged instead.
(def merges-second-when-closer-spec
  {:name 'hierarchical/merges-second-when-closer :universes []
   :type (equality nat
                   (closest-pair (whole 9) (data-nat 0) (whole 4) (data-nat 1))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (closest-pair (whole 9) (data-nat 0)
                                      (whole 4) (data-nat 1)))})

;; Greedy invariant: the merged pair's distance is at most the alternative's
;; (2 <= 6).
(def merged-is-closest-spec
  {:name 'hierarchical/merged-is-closest :universes []
   :type (nnrat-at-most (whole 2) (whole 6))
   :value (at-most-proof (whole 2) (whole 6))})

(def theorem-specs
  [merges-closest-pair-spec merges-second-when-closer-spec merged-is-closest-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-hierarchical-clustering (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.hierarchical-clustering))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
