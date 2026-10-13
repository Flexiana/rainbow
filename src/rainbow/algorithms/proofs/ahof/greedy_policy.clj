(ns rainbow.algorithms.proofs.ahof.greedy-policy
  "AHoF greedy policy extraction: given a state-action value function Q(s, .), the
  greedy policy chooses the action of maximal value,

      pi(s) = argmax_a Q(s, a),   greedy-value(s) = max_a Q(s, a).

  This is the policy-improvement step at the heart of value iteration and policy
  iteration. Classically, when Q is the exact action-value function Q-pi of a
  policy pi, the policy greedy with respect to it is at least as good as pi
  itself (policy improvement, not proved here). That is improvement over the
  policy Q was computed for, not global optimality: being greedy with respect
  to an arbitrary Q, or even to an exact Q-pi, does not make a policy at least
  as good as every other one; only a greedy policy for the optimal Q* is
  optimal. Defined: the greedy action via
  the argmax-index fold and the greedy value via the list-maximum fold. Proved
  native and axiom-free, as worked instances for Q = [5,7,4]: the greedy action
  is 1, the greedy value is 7, and the worked certificates 5 <= 7 and 4 <= 7
  (native nnrat/at-most). Dominance of the greedy value for every Q is not
  proved here. The Q-value estimates are executable / supplied.

  Requires argmax-index/argmax-index, list-maximum/maximum, nnrat/at-most,
  audit/decide-nnrat-at-most, nnrat/decide-at-most-true-sound, and the D63
  checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.greedy-policy`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.algorithms.proofs.list-maximum :as list-maximum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))
(defn- list-maximum-app [xs]
  (function/app (function/const* 'list-maximum/maximum []) xs))
(defn- greedy-action [q]
  (function/app (function/const* 'greedy/action []) q))
(defn- greedy-value [q]
  (function/app (function/const* 'greedy/value []) q))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; greedy-action Q = argmax_a Q(s,a)
(def greedy-action-spec
  {:name 'greedy/action :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['q list-nnrat]] (argmax-index-app 'q))})

;; greedy-value Q = max_a Q(s,a)
(def greedy-value-spec
  {:name 'greedy/value :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value (function/lam [['q list-nnrat]] (list-maximum-app 'q))})

(def definition-specs [greedy-action-spec greedy-value-spec])

;; Theorems -----------------------------------------------------------------

(def q-values (nnrat-list (whole 5) (whole 7) (whole 4)))

;; The greedy action for Q = [5,7,4] is action 1 (value 7).
(def greedy-action-example-spec
  {:name 'greedy/action-example :universes []
   :type (equality nat (greedy-action q-values) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (greedy-action q-values))})

;; The greedy value for Q = [5,7,4] is 7.
(def greedy-value-example-spec
  {:name 'greedy/value-example :universes []
   :type (equality nnrat (greedy-value q-values) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (greedy-value q-values))})

;; Worked certificates 5 <= 7 and 4 <= 7 for Q = [5,7,4]; dominance for every Q
;; is not proved here.
(def dominates-action-zero-spec
  {:name 'greedy/dominates-action-zero :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

(def dominates-action-two-spec
  {:name 'greedy/dominates-action-two :universes []
   :type (nnrat-at-most (whole 4) (whole 7))
   :value (at-most-proof (whole 4) (whole 7))})

(def theorem-specs
  [greedy-action-example-spec greedy-value-example-spec
   dominates-action-zero-spec dominates-action-two-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.argmax-index rainbow.algorithms.proofs.list-maximum])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-greedy-policy (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.greedy-policy))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
