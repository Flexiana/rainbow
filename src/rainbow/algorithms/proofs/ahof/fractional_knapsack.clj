(ns rainbow.algorithms.proofs.ahof.fractional-knapsack
  "AHoF Fractional Knapsack: unlike the 0/1 version (which needs DP), when items
  may be taken in fractional amounts the problem is solved OPTIMALLY by a simple
  greedy rule -- take items in decreasing order of value density (value / weight),
  filling the knapsack and splitting the last item that does not fully fit. The
  ordering decision between two items compares their value densities:

      prefer? density-a density-b = decide (density-b <= density-a)

  (take the higher-density item first), over exact-rational densities. Proved
  native and axiom-free: the priority test; worked instances -- density 3 is
  preferred over density 2; the certificate 2 <= 3 as a native nnrat/at-most;
  and density 2 is not preferred over 5. Optimality of the greedy order (the
  classical exchange argument) is not proved here. The value densities (a
  division) and the fractional fill are executable; what is proved is the greedy
  priority decision at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fractional-knapsack`
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

(defn- prefer? [density-a density-b]
  (function/app (function/const* 'fractional-knapsack/prefer? [])
                density-a density-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; prefer? density-a density-b = decide (density-b <= density-a)
(def prefer-spec
  {:name 'fractional-knapsack/prefer? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['density-a nnrat] ['density-b nnrat]]
                        (decide-at-most 'density-b 'density-a))})

(def definition-specs [prefer-spec])

;; Theorems -----------------------------------------------------------------

;; Item A (density 3) is taken before item B (density 2).
(def prefers-higher-density-spec
  {:name 'fractional-knapsack/prefers-higher-density :universes []
   :type (equality bool (prefer? (whole 3) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefer? (whole 3) (whole 2)))})

;; Certificate: the preferred item's density is at least the other's (2 <= 3).
(def preferred-has-higher-density-spec
  {:name 'fractional-knapsack/preferred-has-higher-density :universes []
   :type (nnrat-at-most (whole 2) (whole 3))
   :value (at-most-proof (whole 2) (whole 3))})

;; A lower-density item (2) is not preferred over a higher one (5).
(def rejects-lower-density-spec
  {:name 'fractional-knapsack/rejects-lower-density :universes []
   :type (equality bool (prefer? (whole 2) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefer? (whole 2) (whole 5)))})

(def theorem-specs
  [prefers-higher-density-spec preferred-has-higher-density-spec
   rejects-lower-density-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-fractional-knapsack (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.fractional-knapsack))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
