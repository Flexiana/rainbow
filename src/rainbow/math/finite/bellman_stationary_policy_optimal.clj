(ns rainbow.math.finite.bellman-stationary-policy-optimal
  "A concrete optimal-policy theorem for exact finite NNRAT Bellman models.

  Earlier generic policy-iteration theorems isolated optimality-fixed-point
  uniqueness as an abstract premise.  This module discharges that premise with
  the exact Bellman uniqueness theorem: a policy value that is a fixed point of
  its policy backup and is greedy-consistent with the optimality operator is
  pointwise equivalent to any Bellman optimal fixed point.

  Carrier exhaustiveness and the exact discount gap/inverse identities remain
  explicit, matching the constructive contraction proof.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-fixed-point-uniqueness
             :as uniqueness]
            [rainbow.math.finite.policy-iteration-optimal
             :as abstract-optimality]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level])
       element source value))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rows-normalized [state action states transition]
  (app (function/const* 'markov/nnrat-rows-normalized [U V])
       state action states transition))
(defn- backup-operator
  [state action states transition reward discount]
  (app (function/const* 'bellman/nnrat-action-backup [U V])
       state action states transition reward discount))
(defn- optimality-step
  [state action actions fallback backup value current]
  (app (function/const* 'value/nnrat-optimality-step [U V])
       state action actions fallback backup value current))

(def stationary-bellman-policy-value-is-optimal-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        optimum-at
        (fn [value state]
          (optimality-step 'S 'A 'actions 'fallback backup value state))
        policy-backup-at
        (fn [value state]
          (app backup value state (app 'policy state)))
        fixed-point
        (fn [value]
          (function/forall
           [['state 'S]]
           (req (optimum-at value 'state) (app value 'state))))
        binders
        [['S type-u]
         ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['actions (exact-finset-of V 'A)]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A nnrat)]
         ['discount nnrat]
         ['fallback (function/arrow 'S 'A)]
         ['fallback-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'fallback 'state)))]
         ['normalized (rows-normalized 'S 'A 'states 'transition)]
         ['state-covered
          (function/forall
           [['state 'S]]
           (source-membership U 'S 'states 'state))]
         ['policy (function/arrow 'S 'A)]
         ['policy-value value-function]
         ['policy-value-fixed
          (function/forall
           [['state 'S]]
           (req (app 'policy-value 'state)
                (policy-backup-at 'policy-value 'state)))]
         ['greedy-consistent
          (function/forall
           [['state 'S]]
           (req (policy-backup-at 'policy-value 'state)
                (optimum-at 'policy-value 'state)))]
         ['optimal-value value-function]
         ['optimal-fixed (fixed-point 'optimal-value)]
         ['gap nnrat]
         ['inverse nnrat]
         ['discount-plus-gap-one
          (req (radd 'discount 'gap) nnrat-one)]
         ['inverse-times-gap-one
          (req (rmul 'inverse 'gap) nnrat-one)]]]
    {:name 'value/nnrat-stationary-bellman-policy-value-is-optimal
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (req (app 'policy-value 'state)
            (app 'optimal-value 'state))))
     :value
     (function/lam
      binders
      (let [fixed-points-unique
            (function/lam
             [['left value-function]
              ['right value-function]
              ['left-fixed (fixed-point 'left)]
              ['right-fixed (fixed-point 'right)]
              ['state 'S]]
             (app
              (function/const*
               'value/nnrat-optimality-fixed-points-unique [U V])
              'S 'A 'states 'actions 'transition 'reward 'discount
              'fallback 'fallback-admissible 'normalized 'state-covered
              'left 'left-fixed 'right 'right-fixed
              'gap 'inverse
              'discount-plus-gap-one 'inverse-times-gap-one
              'state))]
        (function/lam
         [['state 'S]]
         (app
          (function/const*
           'value/nnrat-stationary-policy-value-is-optimal-given-uniqueness
           [U V])
          'S 'A 'actions 'fallback backup
          'policy 'policy-value 'policy-value-fixed 'greedy-consistent
          'optimal-value 'optimal-fixed fixed-points-unique 'state))))}))

(def definition-specs [])
(def theorem-specs [stationary-bellman-policy-value-is-optimal-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(defn extend-environment [env]
  (-> env
      uniqueness/extend-environment
      (extend-specs-if-missing
       :finite-policy-iteration-optimal abstract-optimality/theorem-specs)
      (support/extend-with
       :finite-bellman-stationary-policy-optimal theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
