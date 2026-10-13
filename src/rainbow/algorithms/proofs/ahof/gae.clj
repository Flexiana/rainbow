(ns rainbow.algorithms.proofs.ahof.gae
  "AHoF D42 Generalized Advantage Estimation: estimate the advantage function as
  an exponentially-weighted (by gamma*lambda) sum of temporal-difference errors,

      A_t = delta_t + (gamma*lambda) delta_{t+1} + (gamma*lambda)^2 delta_{t+2} + ...

  trading bias against variance via lambda. A truncated two-step estimate is

      gae2 d0 d1 w = d0 + w * d1        (w = gamma*lambda)

  over exact-rational TD errors and weight. Proved native and axiom-free: the
  weighted-advantage combination; a worked estimate; and that with weight 0 the
  advantage collapses to the one-step TD error delta_t (the high-bias / TD(0) end
  of the lambda spectrum) -- reducing by reflexivity. The TD errors and the value
  baseline are executable; what is proved is the geometrically-weighted advantage
  combination.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gae`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- gae2 [d0 d1 w]
  (function/app (function/const* 'gae/gae2 []) d0 d1 w))

;; Definitions --------------------------------------------------------------

;; gae2 d0 d1 w = d0 + w * d1
(def gae2-spec
  {:name 'gae/gae2 :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['d0 nnrat] ['d1 nnrat] ['w nnrat]]
                        (nnrat-add 'd0 (nnrat-multiply 'w 'd1)))})

(def definition-specs [gae2-spec])

;; Theorems -----------------------------------------------------------------

;; Worked: delta_t = 1, delta_{t+1} = 1, weight gamma*lambda = 1/2 -> A = 3/2.
(def gae2-example-spec
  {:name 'gae/gae2-example :universes []
   :type (equality nnrat
                   (gae2 (whole 1) (whole 1) (fraction 1 1))
                   (fraction 3 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (gae2 (whole 1) (whole 1) (fraction 1 1)))})

;; At weight 0 (lambda = 0), the advantage collapses to the one-step TD error d0.
(def collapses-to-td-spec
  {:name 'gae/collapses-to-td :universes []
   :type (equality nnrat
                   (gae2 (whole 2) (whole 5) (whole 0))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (gae2 (whole 2) (whole 5) (whole 0)))})

(def theorem-specs [gae2-example-spec collapses-to-td-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-gae
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
