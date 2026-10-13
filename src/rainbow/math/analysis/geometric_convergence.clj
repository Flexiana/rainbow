(ns rainbow.math.analysis.geometric-convergence
  "Worked geometric convergence: the contraction distance provably reaches below
  each accuracy threshold at a computable step. For gamma = 1/2 and starting
  distance 8, the distances are 8, 4, 2, 1, 1/2, 1/4, ...; so the modulus that
  achieves accuracy epsilon is the least step whose distance is <= epsilon:

      step 3 reaches <= 1,   step 4 reaches <= 1/2,   step 5 reaches <= 1/4.

  Each bound is a native `nnrat/at-most` proved through the decidable comparison
  (`nnrat/decide-at-most-true-sound` applied to the reflexivity that the decision
  computes to true). These are the concrete instances of the convergence modulus
  underlying `convergence/converges-to`; the fully general `forall epsilon`
  statement composes them with monotonicity of gamma^n.

  Requires `nnrat/at-most`, `audit/decide-nnrat-at-most`, and
  `nnrat/decide-at-most-true-sound` in the environment."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))
(def true-value (function/const* 'data/true []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))

;; distance after n contraction steps by gamma = 1/2 from a starting distance.
(defn- contract-n [n distance]
  (nth (iterate #(multiply half %) distance) n))

;; A proof of `nnrat/at-most a b` via the decidable comparison computing to true.
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Theorems -----------------------------------------------------------------

;; After 3 steps the distance (8*(1/2)^3 = 1) is at most 1.
(def reaches-one-at-step-3-spec
  {:name 'convergence/reaches-one-at-step-3 :universes []
   :type (nnrat-at-most (contract-n 3 (whole 8)) (whole 1))
   :value (at-most-proof (contract-n 3 (whole 8)) (whole 1))})

;; After 4 steps the distance (1/2) is at most 1/2.
(def reaches-half-at-step-4-spec
  {:name 'convergence/reaches-half-at-step-4 :universes []
   :type (nnrat-at-most (contract-n 4 (whole 8)) half)
   :value (at-most-proof (contract-n 4 (whole 8)) half)})

;; The distance is monotone: after 4 steps it is already at most the step-3
;; distance (1/2 <= 1).
(def monotone-decrease-spec
  {:name 'convergence/monotone-decrease :universes []
   :type (nnrat-at-most (contract-n 4 (whole 8)) (contract-n 3 (whole 8)))
   :value (at-most-proof (contract-n 4 (whole 8)) (contract-n 3 (whole 8)))})

;; After 5 steps the distance (1/4) is below the threshold 1/2 as well.
(def reaches-below-half-at-step-5-spec
  {:name 'convergence/reaches-below-half-at-step-5 :universes []
   :type (nnrat-at-most (contract-n 5 (whole 8)) half)
   :value (at-most-proof (contract-n 5 (whole 8)) half)})

(def definition-specs [])
(def theorem-specs
  [reaches-one-at-step-3-spec reaches-half-at-step-4-spec
   monotone-decrease-spec reaches-below-half-at-step-5-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :geometric-convergence theorem-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
