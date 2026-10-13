(ns rainbow.algorithms.proofs.ahof.pbvi
  "AHoF D72 PBVI (Point-Based Value Iteration for POMDPs): maintain value at a finite
  set of belief points, backing up each point's value as the maximum over candidate
  alpha vectors of the value at that belief. With two candidates the backup keeps the
  larger value, preferring candidate 0 when its value is at least candidate 1's:

      prefers-candidate-zero? v0 v1 = decide (v1 <= v0)
      backup-value            v0 v1 = if (v1 <= v0) then v0 else v1   (the larger value)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  backup (max) value, and the switch when candidate 1 is larger. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pbvi`
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
(defn- prefers-candidate-zero? [v0 v1]
  (function/app (function/const* 'pbvi/prefers-candidate-zero? []) v0 v1))
(defn- backup-value [v0 v1]
  (function/app (function/const* 'pbvi/backup-value []) v0 v1))

(def prefers-spec
  {:name 'pbvi/prefers-candidate-zero? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['v0 nnrat] ['v1 nnrat]] (decide-at-most 'v1 'v0))})

(def backup-value-spec
  {:name 'pbvi/backup-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['v0 nnrat] ['v1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'v1 'v0))
                                      (decide-at-most 'v1 'v0) 'v0 'v1))})

(def definition-specs [prefers-spec backup-value-spec])

(def prefers-higher-candidate-spec
  {:name 'pbvi/prefers-higher-candidate :universes []
   :type (equality bool (prefers-candidate-zero? (fraction 3 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-candidate-zero? (fraction 3 3) (fraction 1 1)))})

(def backup-is-maximum-spec
  {:name 'pbvi/backup-is-maximum :universes []
   :type (equality nnrat (backup-value (fraction 3 3) (fraction 1 1)) (fraction 3 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (backup-value (fraction 3 3) (fraction 1 1)))})

(def switches-candidate-spec
  {:name 'pbvi/switches-candidate :universes []
   :type (equality bool (prefers-candidate-zero? (fraction 1 1) (fraction 3 3)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-candidate-zero? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [prefers-higher-candidate-spec backup-is-maximum-spec switches-candidate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-pbvi (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.pbvi))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
