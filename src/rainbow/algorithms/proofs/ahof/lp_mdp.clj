(ns rainbow.algorithms.proofs.ahof.lp-mdp
  "AHoF D24 LP Formulation of an MDP: the optimal value function is the solution of a
  linear program that minimizes the total value subject to the Bellman inequality
  constraints -- for every state-action pair the value must be at least its one-step
  backup R + gamma * E[V']:

      satisfies-bellman? backup value = decide (backup <= value).

  A value that meets or exceeds its backup is LP-feasible for that constraint; a value
  below its backup violates it. Proved native and axiom-free: the constraint decision,
  a feasible and a tight instance, the native at-most feasibility certificate, and a
  violated instance. Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.lp-mdp`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- satisfies-bellman? [backup value]
  (function/app (function/const* 'lp-mdp/satisfies-bellman? []) backup value))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def satisfies-spec
  {:name 'lp-mdp/satisfies-bellman? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['backup nnrat] ['value nnrat]]
                        (decide-at-most 'backup 'value))})

(def definition-specs [satisfies-spec])

;; A value 3/4 above its backup 1/2 is LP-feasible.
(def feasible-value-spec
  {:name 'lp-mdp/feasible-value :universes []
   :type (equality bool (satisfies-bellman? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfies-bellman? (fraction 1 1) (fraction 3 3)))})

;; A value exactly equal to its backup (tight constraint) is still feasible.
(def tight-constraint-spec
  {:name 'lp-mdp/tight-constraint :universes []
   :type (equality bool (satisfies-bellman? (fraction 3 3) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfies-bellman? (fraction 3 3) (fraction 3 3)))})

;; Certificate: a feasible value really is at least its backup (1/2 <= 3/4).
(def feasibility-certificate-spec
  {:name 'lp-mdp/feasibility-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; A value 1/2 below its backup 3/4 violates the constraint.
(def violated-constraint-spec
  {:name 'lp-mdp/violated-constraint :universes []
   :type (equality bool (satisfies-bellman? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (satisfies-bellman? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [feasible-value-spec tight-constraint-spec feasibility-certificate-spec
   violated-constraint-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-lp-mdp (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.lp-mdp))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
