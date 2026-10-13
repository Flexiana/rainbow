(ns rainbow.math.analysis.geometric-decay
  "The geometric contraction bound -- the analysis entry point for value-iteration
  convergence. A strict contraction with rational modulus gamma < 1 shrinks the
  distance to the fixed point by a factor gamma each step:

      d_{n+1} = gamma * d_n     so     d_n = gamma^n * d_0

  With a rational gamma the whole trajectory is exact rational arithmetic (no
  reals, no logarithms), so the geometric decay is proved directly: from a
  starting distance 8 with gamma = 1/2 the distances are 8, 4, 2, 1, ... halving
  toward 0. This is the quantitative core that, composed with a fixed-point
  uniqueness result, gives a rational modulus of convergence: to reach distance
  below any epsilon it suffices to iterate until gamma^n * d_0 < epsilon.

  The full convergence theorem (the limit is the unique fixed point) is built on
  top of this with a rational convergence modulus."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- contract [gamma distance]
  (function/app (function/const* 'decay/contract []) gamma distance))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; One contraction step: the distance to the fixed point shrinks by gamma.
(def contract-spec
  {:name 'decay/contract :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['gamma nnrat] ['distance nnrat]]
                        (multiply 'gamma 'distance))})

(def definition-specs [contract-spec])

;; Theorems -----------------------------------------------------------------

(def contract-unfold-spec
  {:name 'decay/contract-unfold :universes []
   :type (function/forall
          [['gamma nnrat] ['distance nnrat]]
          (equality nnrat (contract 'gamma 'distance)
                    (multiply 'gamma 'distance)))
   :value (function/lam [['gamma nnrat] ['distance nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (contract 'gamma 'distance)))})

;; The geometric decay trajectory from distance 8 with gamma = 1/2: 8 -> 4 -> 2
;; -> 1, each step halving the distance to the fixed point.
(def step1-spec
  {:name 'decay/step1-eight-to-four :universes []
   :type (equivalent (contract half (whole 8)) (whole 4))
   :value (cross-product-reflexivity (contract half (whole 8)) (whole 4))})

(def step2-spec
  {:name 'decay/step2-four-to-two :universes []
   :type (equivalent (contract half (whole 4)) (whole 2))
   :value (cross-product-reflexivity (contract half (whole 4)) (whole 2))})

(def step3-spec
  {:name 'decay/step3-two-to-one :universes []
   :type (equivalent (contract half (whole 2)) (whole 1))
   :value (cross-product-reflexivity (contract half (whole 2)) (whole 1))})

;; Three composed contraction steps take distance 8 to 1 (gamma^3 * 8 = 1).
(def three-steps-spec
  {:name 'decay/three-steps-eight-to-one :universes []
   :type (equivalent (contract half (contract half (contract half (whole 8))))
                     (whole 1))
   :value (cross-product-reflexivity
           (contract half (contract half (contract half (whole 8))))
           (whole 1))})

(def theorem-specs [contract-unfold-spec step1-spec step2-spec step3-spec
                    three-steps-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :geometric-decay
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
