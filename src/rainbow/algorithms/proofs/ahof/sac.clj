(ns rainbow.algorithms.proofs.ahof.sac
  "AHoF D45 Soft Actor-Critic: an off-policy actor-critic that optimizes a
  MAXIMUM-ENTROPY objective, augmenting the reward with an entropy bonus so the
  policy stays as stochastic as possible while succeeding -- improving
  exploration and robustness. The soft (entropy-regularized) value of a state is

      soft-value reward alpha entropy = reward + alpha * entropy

  over exact-rational reward, temperature alpha, and policy entropy. Proved
  native and axiom-free: the soft-value combination; a worked soft value; and
  that at temperature 0 (alpha = 0) the soft value collapses to the plain reward
  (recovering standard RL) -- reducing by reflexivity. The critic, the reward,
  and the entropy estimate are executable; what is proved is the
  entropy-regularized soft-value combination.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.sac`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- soft-value [reward alpha entropy]
  (function/app (function/const* 'sac/soft-value []) reward alpha entropy))

;; Definitions --------------------------------------------------------------

;; soft-value reward alpha entropy = reward + alpha * entropy
(def soft-value-spec
  {:name 'sac/soft-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['reward nnrat] ['alpha nnrat] ['entropy nnrat]]
                        (nnrat-add 'reward (nnrat-multiply 'alpha 'entropy)))})

(def definition-specs [soft-value-spec])

;; Theorems -----------------------------------------------------------------

;; Worked: reward 1, temperature 1/2, entropy 1 -> soft value 3/2.
(def soft-value-example-spec
  {:name 'sac/soft-value-example :universes []
   :type (equality nnrat
                   (soft-value (whole 1) (fraction 1 1) (whole 1))
                   (fraction 3 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (soft-value (whole 1) (fraction 1 1) (whole 1)))})

;; At temperature 0, the soft value collapses to the plain reward (standard RL).
(def collapses-to-reward-spec
  {:name 'sac/collapses-to-reward :universes []
   :type (equality nnrat
                   (soft-value (whole 2) (whole 0) (whole 5))
                   (whole 2))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (soft-value (whole 2) (whole 0) (whole 5)))})

(def theorem-specs [soft-value-example-spec collapses-to-reward-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-sac (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.sac))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
