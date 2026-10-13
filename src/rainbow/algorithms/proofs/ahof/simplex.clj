(ns rainbow.algorithms.proofs.ahof.simplex
  "AHoF O54 Simplex Algorithm -- the minimum-ratio test that chooses the leaving
  variable (pivot row) each iteration. Having chosen an entering column, the
  simplex method pivots on the row with the smallest ratio of right-hand side to
  positive pivot-column entry, keeping the basic solution feasible:

      pivot-ratio r1 r2 = min(r1, r2)

  over the exact-rational ratios (the two-row case; the general test folds this
  over all rows with a positive column entry). Proved native and axiom-free:
  worked instances with ratios 7 and 2 -- pivot-ratio 7 2 = 2, and the worked
  certificates pivot-ratio 7 2 <= 7 and pivot-ratio 7 2 <= 2. The tableau pivot,
  entering-column selection (Bland's rule / steepest edge), and optimality test
  are executable concerns; what is proved here is the min-ratio choice at this
  instance. That the min-ratio step is the largest that preserves feasibility is
  the classical property of the test and is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.simplex`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- nnrat-min-term [a b] (if-value (decide-at-most a b) a b))

(defn- pivot-ratio [r1 r2]
  (function/app (function/const* 'simplex/pivot-ratio []) r1 r2))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; pivot-ratio r1 r2 = min(r1, r2)   (smallest ratio wins the pivot)
(def pivot-ratio-spec
  {:name 'simplex/pivot-ratio :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['r1 nnrat] ['r2 nnrat]]
                        (nnrat-min-term 'r1 'r2))})

(def definition-specs [pivot-ratio-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; The pivot takes the smaller ratio (rows with ratios 7 and 2 -> 2).
(def pivot-example-spec
  {:name 'simplex/pivot-example :universes []
   :type (equality nnrat (pivot-ratio (whole 7) (whole 2)) (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (pivot-ratio (whole 7) (whole 2)))})

;; Worked certificate: pivot-ratio 7 2 <= 7.
(def pivot-below-r1-spec
  {:name 'simplex/pivot-below-r1 :universes []
   :type (nnrat-at-most (pivot-ratio (whole 7) (whole 2)) (whole 7))
   :value (at-most-proof (pivot-ratio (whole 7) (whole 2)) (whole 7))})

;; Worked certificate: pivot-ratio 7 2 <= 2.
(def pivot-below-r2-spec
  {:name 'simplex/pivot-below-r2 :universes []
   :type (nnrat-at-most (pivot-ratio (whole 7) (whole 2)) (whole 2))
   :value (at-most-proof (pivot-ratio (whole 7) (whole 2)) (whole 2))})

(def theorem-specs
  [pivot-example-spec pivot-below-r1-spec pivot-below-r2-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-simplex
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
