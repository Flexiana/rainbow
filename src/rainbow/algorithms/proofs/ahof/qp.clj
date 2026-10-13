(ns rainbow.algorithms.proofs.ahof.qp
  "AHoF O56 Quadratic Programming: minimize a convex quadratic objective subject
  to linear constraints, typically by encoding the KKT stationarity system. The
  (scalar / separable) quadratic objective value is

      objective q x c = q * x * x + c * x

  over exact nonnegative rationals (the general form is
  1/2 x^T Q x + c^T x; here the 1/2 is folded into q and the state is scalar or a
  separable coordinate). Proved native and axiom-free: the objective evaluation
  and worked instances that reduce by reflexivity, plus the gradient stationarity
  reading (the minimizer solves the KKT system, executable). The matrix Q, the
  constraint handling, and the linear-algebra solve are executable concerns; what
  is proved here is the deterministic quadratic-form evaluation.

  Requires nnrat/add and nnrat/multiply (in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.qp`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- objective [q x c]
  (function/app (function/const* 'qp/objective []) q x c))

;; Definitions --------------------------------------------------------------

;; objective q x c = q * x * x + c * x
(def objective-spec
  {:name 'qp/objective :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['q nnrat] ['x nnrat] ['c nnrat]]
                        (nnrat-add (nnrat-multiply 'q
                                                   (nnrat-multiply 'x 'x))
                                   (nnrat-multiply 'c 'x)))})

(def definition-specs [objective-spec])

;; Theorems -----------------------------------------------------------------

(def objective-unfold-spec
  {:name 'qp/objective-unfold :universes []
   :type (function/forall
          [['q nnrat] ['x nnrat] ['c nnrat]]
          (equality nnrat
                    (objective 'q 'x 'c)
                    (nnrat-add (nnrat-multiply 'q (nnrat-multiply 'x 'x))
                               (nnrat-multiply 'c 'x))))
   :value (function/lam [['q nnrat] ['x nnrat] ['c nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (objective 'q 'x 'c)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked objective: q 2, x 3, c 1 -> 2*9 + 1*3 = 21.
(def objective-example-spec
  {:name 'qp/objective-example :universes []
   :type (equality nnrat (objective (whole 2) (whole 3) (whole 1)) (whole 21))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (objective (whole 2) (whole 3) (whole 1)))})

;; At x = 0 the objective vanishes (worked q 5, c 3): 5*0 + 3*0 = 0.
(def objective-at-zero-spec
  {:name 'qp/objective-at-zero :universes []
   :type (equality nnrat
                   (objective (whole 5) (function/const* 'nnrat/zero [])
                              (whole 3))
                   (function/const* 'nnrat/zero []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (objective (whole 5) (function/const* 'nnrat/zero [])
                                   (whole 3)))})

(def theorem-specs
  [objective-unfold-spec objective-example-spec objective-at-zero-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-qp (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.qp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
