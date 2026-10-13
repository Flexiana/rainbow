(ns rainbow.algorithms.proofs.adadelta
  "AHoF O23 Adadelta: the learning-rate-free update scale. Adadelta needs no
  base learning rate; instead it scales the gradient by the ratio of the root
  mean square of recent updates to the root mean square of recent gradients:

      scale = RMS[update] / RMS[gradient] = sqrt(accum-update) / sqrt(accum-grad)

  On perfect-square accumulators both roots are exact, so the scale is an exact
  rational division of the two roots (witnessed by root*root ~ accumulator). With
  an update accumulator of 4 (root 2) and a gradient accumulator of 9 (root 3)
  the scale is 2/3 -- a dimensionless step size derived entirely from the running
  statistics. The accumulator decay and the general irrational sqrt stay in the
  executable reference and are not claimed.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.adadelta`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- fraction [num den-predecessor]
  (function/app (function/const* 'nnrat/make []) (data-nat num)
                (data-nat den-predecessor)))

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
  (function/app (function/const* 'adadelta/square-root? []) radicand root))
(defn- scale [update-root gradient-root]
  (function/app (function/const* 'adadelta/scale []) update-root gradient-root))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; A root witness: root*root ~ radicand.
(def square-root?-spec
  {:name 'adadelta/square-root? :kind :definition :universes []
   :type (function/arrow nnrat nnrat 'Prop)
   :value (function/lam [['radicand nnrat] ['root nnrat]]
                        (equivalent (multiply 'root 'root) 'radicand))})

;; The learning-rate-free scale: RMS[update] / RMS[gradient].
(def scale-spec
  {:name 'adadelta/scale :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['update-root nnrat] ['gradient-root nnrat]]
                        (divide 'update-root 'gradient-root))})

(def definition-specs [square-root?-spec scale-spec])

;; Theorems -----------------------------------------------------------------

;; 3 is a square root of 9 (the gradient accumulator's root).
(def three-is-root-of-nine-spec
  {:name 'adadelta/three-is-root-of-nine :universes []
   :type (square-root? (whole 9) (whole 3))
   :value (cross-product-reflexivity (multiply (whole 3) (whole 3)) (whole 9))})

;; Update accumulator 4 (root 2) over gradient accumulator 9 (root 3) gives the
;; dimensionless scale 2/3.
(def scale-example-spec
  {:name 'adadelta/scale-example :universes []
   :type (equivalent (scale (whole 2) (whole 3)) (fraction 2 2))
   :value (cross-product-reflexivity (scale (whole 2) (whole 3)) (fraction 2 2))})

;; A larger recent update than gradient gives a scale above one: 3/2.
(def scale-above-one-example-spec
  {:name 'adadelta/scale-above-one-example :universes []
   :type (equivalent (scale (whole 3) (whole 2)) (fraction 3 1))
   :value (cross-product-reflexivity (scale (whole 3) (whole 2)) (fraction 3 1))})

(def theorem-specs
  [three-is-root-of-nine-spec scale-example-spec scale-above-one-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :adadelta (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.adadelta))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
