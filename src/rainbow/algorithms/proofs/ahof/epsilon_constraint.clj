(ns rainbow.algorithms.proofs.ahof.epsilon-constraint
  "AHoF O67 Epsilon-Constraint Method (multi-objective): optimize one objective while
  the others are turned into inequality constraints f_i <= epsilon_i. A candidate is
  feasible for the constrained objective exactly when its value is within the epsilon
  bound:

      feasible? value epsilon = decide (value <= epsilon)

  over exact rationals. Proved native and axiom-free: the feasibility decision; that a
  value within the bound is feasible; the certificate that a feasible value really is
  at most epsilon (native nnrat/at-most); and that a value exceeding the bound is
  infeasible. Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.epsilon-constraint`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

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
(defn- feasible? [value epsilon]
  (function/app (function/const* 'epsilon-constraint/feasible? []) value epsilon))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; feasible? value epsilon = decide (value <= epsilon)
(def feasible-spec
  {:name 'epsilon-constraint/feasible? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['value nnrat] ['epsilon nnrat]]
                        (decide-at-most 'value 'epsilon))})

(def definition-specs [feasible-spec])

;; A value 1/2 within the epsilon bound 3/4 is feasible.
(def within-bound-feasible-spec
  {:name 'epsilon-constraint/within-bound-feasible :universes []
   :type (equality bool (feasible? (fraction 1 1) (fraction 3 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (feasible? (fraction 1 1) (fraction 3 3)))})

;; Certificate: a feasible value is at most epsilon (1/2 <= 3/4).
(def feasible-within-epsilon-spec
  {:name 'epsilon-constraint/feasible-within-epsilon :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; A value 3/4 exceeding the epsilon bound 1/2 is infeasible.
(def over-bound-infeasible-spec
  {:name 'epsilon-constraint/over-bound-infeasible :universes []
   :type (equality bool (feasible? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (feasible? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [within-bound-feasible-spec feasible-within-epsilon-spec
   over-bound-infeasible-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-epsilon-constraint
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
