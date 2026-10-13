(ns rainbow.algorithms.proofs.ahof.variable-elimination
  "AHoF D3 Variable Elimination: exact inference by successively eliminating
  (marginalizing out) variables from the factor graph. Eliminating a variable
  sums the factor over that variable's values; for a binary variable the marginal
  is the sum of the two slices:

      marginalize f-false f-true = f-false + f-true

  over exact nonnegative rational factor entries (the general case folds the sum
  over all values of the eliminated variable). Proved native and axiom-free: the
  marginalization sum, and the guarantee that a marginal dominates each of its
  summands (f-true <= marginal), so summing out never loses probability mass. The
  variable elimination ordering (a pluggable strategy) and the factor products
  that precede each elimination are executable concerns; what is proved here is
  the marginalization sum and its mass-preservation bound.

  Requires nnrat/add, nnrat/at-most, and the decidable nnrat order (D63).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.variable-elimination`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- marginalize [f-false f-true]
  (function/app (function/const* 'variable-elimination/marginalize [])
                f-false f-true))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; marginalize f-false f-true = f-false + f-true
(def marginalize-spec
  {:name 'variable-elimination/marginalize :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['f-false nnrat] ['f-true nnrat]]
                        (nnrat-add 'f-false 'f-true))})

(def definition-specs [marginalize-spec])

;; Theorems -----------------------------------------------------------------

(def marginalize-unfold-spec
  {:name 'variable-elimination/marginalize-unfold :universes []
   :type (function/forall
          [['f-false nnrat] ['f-true nnrat]]
          (equality nnrat
                    (marginalize 'f-false 'f-true)
                    (nnrat-add 'f-false 'f-true)))
   :value (function/lam [['f-false nnrat] ['f-true nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (marginalize 'f-false 'f-true)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked marginal: factor slices 3 and 4 -> 3 + 4 = 7.
(def marginalize-example-spec
  {:name 'variable-elimination/marginalize-example :universes []
   :type (equality nnrat (marginalize (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (marginalize (whole 3) (whole 4)))})

;; Mass preservation: the marginal dominates a summand (4 <= 7), so summing out
;; never loses probability mass.
(def marginal-dominates-slice-spec
  {:name 'variable-elimination/marginal-dominates-slice :universes []
   :type (nnrat-at-most (whole 4) (marginalize (whole 3) (whole 4)))
   :value (at-most-proof (whole 4) (marginalize (whole 3) (whole 4)))})

(def theorem-specs
  [marginalize-unfold-spec marginalize-example-spec
   marginal-dominates-slice-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-variable-elimination
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
