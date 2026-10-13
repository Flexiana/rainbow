(ns rainbow.algorithms.proofs.ahof.state-abstraction
  "AHoF V52 Discrete State Abstraction (classical: map concrete states to abstract cells
  of a partition). This module does NOT model an abstraction map or a partition; it
  defines a PROXIMITY test, true when the distance between two states is within a radius:

      same-cell? distance radius = decide (distance <= radius).
  Proximity is not transitive, so it cannot in general represent equality of abstract
  cells: with radius 1 and states 0, 3/4, 3/2 both adjacent pairs pass while the endpoints
  (distance 3/2) fail. Proved native and axiom-free, as worked instances: distance 1/2
  within radius 3/4 passes, distance 1/2 at radius 1/2 passes, the certificate
  1/2 <= 3/4, and distance 3/4 at radius 1/2 fails. Requires audit/decide-nnrat-at-most,
  nnrat/at-most, nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.state-abstraction`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- pred [a b] (function/app (function/const* 'abstraction/same-cell? []) a b))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def pred-spec
  {:name 'abstraction/same-cell? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['distance nnrat] ['radius nnrat]] (decide-at-most 'distance 'radius))})

(def definition-specs [pred-spec])

(def within-cell-same-spec
  {:name 'abstraction/within-cell-same :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 3 3)))})

(def boundary-same-spec
  {:name 'abstraction/boundary-same :universes []
   :type (equality bool (pred (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 1 1) (fraction 1 1)))})

(def abstraction-certificate-spec
  {:name 'abstraction/abstraction-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def across-cell-different-spec
  {:name 'abstraction/across-cell-different :universes []
   :type (equality bool (pred (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (pred (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [within-cell-same-spec boundary-same-spec abstraction-certificate-spec across-cell-different-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-state-abstraction
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
