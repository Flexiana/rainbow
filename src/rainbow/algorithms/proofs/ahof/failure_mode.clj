(ns rainbow.algorithms.proofs.ahof.failure-mode
  "AHoF V58 Failure Mode Characterization: cluster observed failures into modes and
  assign a new failure to a mode when its distance to the mode's centroid is within
  the mode radius:

      in-mode? distance radius = decide (distance <= radius).

  A failure at distance 1/2 from a centroid with radius 3/4 belongs to that mode; a
  failure at distance 3/4 with radius 1/2 is outside it (a new mode). Proved native
  and axiom-free (decision, in-mode and boundary instances, at-most membership
  certificate, out-of-mode). Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.failure-mode`
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
(defn- in-mode? [distance radius]
  (function/app (function/const* 'failure-mode/in-mode? []) distance radius))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def in-mode-spec
  {:name 'failure-mode/in-mode? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['distance nnrat] ['radius nnrat]]
                        (decide-at-most 'distance 'radius))})

(def definition-specs [in-mode-spec])

(def within-radius-in-mode-spec
  {:name 'failure-mode/within-radius-in-mode :universes []
   :type (equality bool (in-mode? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-mode? (fraction 1 1) (fraction 3 3)))})

(def boundary-in-mode-spec
  {:name 'failure-mode/boundary-in-mode :universes []
   :type (equality bool (in-mode? (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-mode? (fraction 1 1) (fraction 1 1)))})

(def membership-certificate-spec
  {:name 'failure-mode/membership-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def outside-radius-new-mode-spec
  {:name 'failure-mode/outside-radius-new-mode :universes []
   :type (equality bool (in-mode? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-mode? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [within-radius-in-mode-spec boundary-in-mode-spec membership-certificate-spec
   outside-radius-new-mode-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-failure-mode
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
