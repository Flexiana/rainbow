(ns rainbow.algorithms.proofs.adaptive-gradient
  "AHoF O21 AdaGrad: the adaptive per-parameter learning rate. AdaGrad divides a
  base rate by the square root of the accumulated squared gradient:

      rate = base-rate / sqrt(accumulator)

  Exact square roots are not rational in general, so this is proved on the
  perfect-square instances that matter for worked trajectories: a root is
  witnessed by `square-root?` (root * root ~ accumulator, proven on the rational
  cross-product), and the adaptive rate is then the exact division base/root.
  With accumulator 4 the root is 2 and a base rate 1 gives adaptive rate 1/2.
  The general irrational sqrt stays unclaimed; the gradient step around the rate
  stays in the executable reference.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.adaptive-gradient`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def one (function/const* 'nnrat/one []))
(def half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
;; nnrat/make takes (numerator, denominator-PREDECESSOR); (whole n) = n/1.
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- square-root? [radicand root]
  (function/app (function/const* 'adagrad/square-root? []) radicand root))
(defn- rate [base-rate root]
  (function/app (function/const* 'adagrad/rate []) base-rate root))

;; Proof of `left ~ right` by reflexivity on the reduced nat cross-product.
(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; `root` is a square root of `radicand` when root*root ~ radicand.
(def square-root?-spec
  {:name 'adagrad/square-root? :kind :definition :universes []
   :type (function/arrow nnrat nnrat 'Prop)
   :value (function/lam [['radicand nnrat] ['root nnrat]]
                        (equivalent (multiply 'root 'root) 'radicand))})

;; The adaptive learning rate: base rate divided by the (witnessed) root.
(def rate-spec
  {:name 'adagrad/rate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['base-rate nnrat] ['root nnrat]]
                        (divide 'base-rate 'root))})

(def definition-specs [square-root?-spec rate-spec])

;; Theorems -----------------------------------------------------------------

;; 2 is a square root of 4.
(def two-is-root-of-four-spec
  {:name 'adagrad/two-is-root-of-four :universes []
   :type (square-root? (whole 4) (whole 2))
   :value (cross-product-reflexivity (multiply (whole 2) (whole 2)) (whole 4))})

;; 3 is a square root of 9.
(def three-is-root-of-nine-spec
  {:name 'adagrad/three-is-root-of-nine :universes []
   :type (square-root? (whole 9) (whole 3))
   :value (cross-product-reflexivity (multiply (whole 3) (whole 3)) (whole 9))})

(def rate-unfold-spec
  {:name 'adagrad/rate-unfold :universes []
   :type (function/forall
          [['base-rate nnrat] ['root nnrat]]
          (equality nnrat (rate 'base-rate 'root)
                    (divide 'base-rate 'root)))
   :value (function/lam [['base-rate nnrat] ['root nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (rate 'base-rate 'root)))})

;; With accumulator 4 (root 2) a base rate of 1 gives adaptive rate 1/2.
(def adaptive-rate-example-spec
  {:name 'adagrad/adaptive-rate-example :universes []
   :type (equivalent (rate one (whole 2)) half)
   :value (cross-product-reflexivity (rate one (whole 2)) half)})

(def theorem-specs
  [two-is-root-of-four-spec three-is-root-of-nine-spec
   rate-unfold-spec adaptive-rate-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :adaptive-gradient
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
