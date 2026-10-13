(ns rainbow.algorithms.proofs.ahof.rollout
  "AHoF D32 Rollout with Heuristic: estimate a state's value by simulating the
  rollout policy forward and averaging the returns. The return of a single
  simulated trajectory is the (discounted) sum of its rewards; here the two-step
  undiscounted return is

      trajectory-return r1 r2 = r1 + r2

  over exact nonnegative rationals (the value estimate averages this over several
  simulations). Proved native and axiom-free: the trajectory return, and the
  guarantee that a return dominates each of its reward steps (r1 <= return), so a
  rollout with a nonnegative reward step never underestimates that step's
  contribution. The rollout policy, the simulation, and the mean over
  trajectories (a division) are executable concerns; what is proved here is the
  deterministic return accumulation.

  Requires nnrat/add, nnrat/at-most, and the decidable nnrat order (D63).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rollout`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- trajectory-return [r1 r2]
  (function/app (function/const* 'rollout/trajectory-return []) r1 r2))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; trajectory-return r1 r2 = r1 + r2
(def trajectory-return-spec
  {:name 'rollout/trajectory-return :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['r1 nnrat] ['r2 nnrat]] (nnrat-add 'r1 'r2))})

(def definition-specs [trajectory-return-spec])

;; Theorems -----------------------------------------------------------------

(def trajectory-return-unfold-spec
  {:name 'rollout/trajectory-return-unfold :universes []
   :type (function/forall
          [['r1 nnrat] ['r2 nnrat]]
          (equality nnrat
                    (trajectory-return 'r1 'r2)
                    (nnrat-add 'r1 'r2)))
   :value (function/lam [['r1 nnrat] ['r2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (trajectory-return 'r1 'r2)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked return: rewards 3 and 4 -> 7.
(def trajectory-return-example-spec
  {:name 'rollout/trajectory-return-example :universes []
   :type (equality nnrat (trajectory-return (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (trajectory-return (whole 3) (whole 4)))})

;; A return dominates a reward step (3 <= 7), so no step is underestimated.
(def return-dominates-step-spec
  {:name 'rollout/return-dominates-step :universes []
   :type (nnrat-at-most (whole 3) (trajectory-return (whole 3) (whole 4)))
   :value (at-most-proof (whole 3) (trajectory-return (whole 3) (whole 4)))})

(def theorem-specs
  [trajectory-return-unfold-spec trajectory-return-example-spec
   return-dominates-step-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-rollout (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.rollout))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
