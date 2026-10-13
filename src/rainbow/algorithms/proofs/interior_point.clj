(ns rainbow.algorithms.proofs.interior-point
  "AHoF O50 Interior Point / Barrier Method: the transform that keeps iterates
  strictly feasible by adding a barrier term that grows as a constraint slack
  approaches zero:

      barrier-objective = objective + mu * (1 / slack)

  where `slack` is the (positive) distance to a constraint boundary and `mu` is
  the barrier parameter, shrunk toward zero across outer iterations. The textbook
  log barrier -mu*sum(log slack) is not exact-rational, so this uses the rational
  inverse barrier mu/slack (both keep iterates interior and diverge at the
  boundary); the log form stays an executable concern. What is proved is the
  barrier-objective recurrence and worked instances via exact division.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.interior-point`
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

(defn- add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- divide [l r] (function/app (function/const* 'nnrat/divide []) l r))
(defn- equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- barrier-objective [objective mu slack]
  (function/app (function/const* 'barrier/objective []) objective mu slack))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; barrier-objective = objective + mu / slack
(def barrier-objective-spec
  {:name 'barrier/objective :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['objective nnrat] ['mu nnrat] ['slack nnrat]]
                        (add 'objective (divide 'mu 'slack)))})

(def definition-specs [barrier-objective-spec])

;; Theorems -----------------------------------------------------------------

(def barrier-objective-unfold-spec
  {:name 'barrier/objective-unfold :universes []
   :type (function/forall
          [['objective nnrat] ['mu nnrat] ['slack nnrat]]
          (equality nnrat (barrier-objective 'objective 'mu 'slack)
                    (add 'objective (divide 'mu 'slack))))
   :value (function/lam [['objective nnrat] ['mu nnrat] ['slack nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (barrier-objective 'objective 'mu 'slack)))})

;; A unit slack: objective 1, mu 2, slack 1 -> 1 + 2/1 = 3.
(def unit-slack-example-spec
  {:name 'barrier/unit-slack-example :universes []
   :type (equivalent (barrier-objective (whole 1) (whole 2) (whole 1)) (whole 3))
   :value (cross-product-reflexivity
           (barrier-objective (whole 1) (whole 2) (whole 1)) (whole 3))})

;; A wider slack softens the barrier: objective 1, mu 2, slack 2 -> 1 + 2/2 = 2.
(def wide-slack-example-spec
  {:name 'barrier/wide-slack-example :universes []
   :type (equivalent (barrier-objective (whole 1) (whole 2) (whole 2)) (whole 2))
   :value (cross-product-reflexivity
           (barrier-objective (whole 1) (whole 2) (whole 2)) (whole 2))})

(def theorem-specs [barrier-objective-unfold-spec unit-slack-example-spec
                    wide-slack-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :interior-point (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.interior-point))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
