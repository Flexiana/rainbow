(ns rainbow.algorithms.proofs.ahof.kmeans
  "AHoF K-Means Clustering (Lloyd's algorithm): partition points into k clusters by
  alternating an ASSIGNMENT step (assign each point to the nearest cluster centroid)
  and an UPDATE step (move each centroid to the mean of its assigned points), until
  assignments stop changing. Classically, the within-cluster variance decreases
  monotonically, which guarantees convergence (not proved here). The assignment
  step selects, for a point, the closer of
  two candidate centroids by (squared) distance:

      assign da ca db cb = if da <= db then ca else cb

  (return the id of the nearer centroid), over exact-rational distances. Proved
  native and axiom-free: the nearest-centroid assignment; a worked assignment; and
  the certificate, for the worked point, that the chosen centroid's distance is at
  most the alternative's (2 <= 7, native nnrat/at-most). The centroid update (a mean)
  and the distance computation are executable; what is proved is the
  nearest-centroid assignment.

  Requires nat, audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kmeans`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- assign [da ca db cb]
  (function/app (function/const* 'kmeans/assign []) da ca db cb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; assign da ca db cb = if da <= db then ca else cb
(def assign-spec
  {:name 'kmeans/assign :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat nat nat)
   :value (function/lam [['da nnrat] ['ca nat] ['db nnrat] ['cb nat]]
                        (if-nat (decide-at-most 'da 'db) 'ca 'cb))})

(def definition-specs [assign-spec])

;; Theorems -----------------------------------------------------------------

;; Centroid 0 at distance 2 is nearer than centroid 1 at distance 7: assign to 0.
(def assigns-to-nearest-spec
  {:name 'kmeans/assigns-to-nearest :universes []
   :type (equality nat
                   (assign (whole 2) (data-nat 0) (whole 7) (data-nat 1))
                   (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (assign (whole 2) (data-nat 0) (whole 7) (data-nat 1)))})

;; When the second centroid is nearer, the point joins that cluster.
(def assigns-to-second-when-nearer-spec
  {:name 'kmeans/assigns-to-second-when-nearer :universes []
   :type (equality nat
                   (assign (whole 9) (data-nat 0) (whole 3) (data-nat 1))
                   (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (assign (whole 9) (data-nat 0) (whole 3) (data-nat 1)))})

;; Certificate: the assigned centroid's distance is at most the alternative's
;; (2 <= 7), so the point joins its closest cluster.
(def assigned-is-nearest-spec
  {:name 'kmeans/assigned-is-nearest :universes []
   :type (nnrat-at-most (whole 2) (whole 7))
   :value (at-most-proof (whole 2) (whole 7))})

(def theorem-specs
  [assigns-to-nearest-spec assigns-to-second-when-nearer-spec
   assigned-is-nearest-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-kmeans
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
