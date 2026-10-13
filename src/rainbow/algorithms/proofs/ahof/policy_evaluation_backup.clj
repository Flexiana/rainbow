(ns rainbow.algorithms.proofs.ahof.policy-evaluation-backup
  "AHoF D-family Policy Evaluation: the evaluation half of policy iteration.
  For a fixed policy pi, the state value satisfies the linear Bellman
  expectation equation; a one-step backup is

      bellman-eval reward gamma next-value = reward + gamma * next-value

  where reward is the expected immediate reward under pi and next-value is the
  (discounted) value of the successor state. Classically, iterating this backup
  converges to the policy's value function (a contraction with modulus gamma < 1);
  that is not proved here. Proved native and axiom-free: the backup combination; a
  worked backup; and a worked myopic case (reward 4, discount 0, next-value 9
  gives value 4: the immediate reward) -- reducing by reflexivity. The
  transition/reward model is executable; what is proved is the Bellman
  expectation backup.

  Requires nnrat/add, nnrat/multiply (both in the D63 checkpoint).

  NOTE ON THE NAMESPACE: this proof originally occupied
  `rainbow.algorithms.proofs.ahof.policy-evaluation`, whose previous contents it replaced.
  Those contents were the `ahof-d20/*` declarations that the AHoF D20 ledger
  entry names as its specification, so replacing them silently invalidated a
  credited catalog row. The original module is restored under its own name and
  this proof lives here.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.policy-evaluation-backup`
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

(defn- bellman-eval [reward gamma next-value]
  (function/app (function/const* 'policy-eval/backup []) reward gamma next-value))

;; Definitions --------------------------------------------------------------

;; bellman-eval reward gamma next-value = reward + gamma * next-value
(def backup-spec
  {:name 'policy-eval/backup :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['reward nnrat] ['gamma nnrat] ['next-value nnrat]]
                        (nnrat-add 'reward
                                   (nnrat-multiply 'gamma 'next-value)))})

(def definition-specs [backup-spec])

;; Theorems -----------------------------------------------------------------

;; Worked backup: reward 1, discount 1/2, next-value 3 -> value 5/2.
(def backup-example-spec
  {:name 'policy-eval/backup-example :universes []
   :type (equality nnrat
                   (bellman-eval (whole 1) (fraction 1 1) (whole 3))
                   (fraction 5 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (bellman-eval (whole 1) (fraction 1 1) (whole 3)))})

;; Worked myopic case: at discount 0 the value is the immediate reward 4.
(def myopic-at-zero-discount-spec
  {:name 'policy-eval/myopic-at-zero-discount :universes []
   :type (equality nnrat
                   (bellman-eval (whole 4) (whole 0) (whole 9))
                   (whole 4))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (bellman-eval (whole 4) (whole 0) (whole 9)))})

(def theorem-specs [backup-example-spec myopic-at-zero-discount-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-policy-evaluation (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.policy-evaluation-backup))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
