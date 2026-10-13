(ns rainbow.math.finite.policy-iteration-optimal
  "Stationary finite-policy improvement implies the optimal Bellman equation.

  The proof keeps optimality-step and finite argmax opaque.  Stationarity is
  represented by the two semantic facts it supplies at every state: the
  policy-value fixed-point equation and greedy consistency.  Their transitive
  composition gives an optimality fixed point.  A separate corollary isolates
  fixed-point uniqueness as the only additional ingredient needed to identify
  that value with an optimum.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.greedy-optimal :as greedy-optimal]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- equivalent-symmetric [left right proof]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right proof))

(defn- equivalent-transitive [left middle right first-step second-step]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first-step second-step))

(defn- optimality-step
  [state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-optimality-step [U V])
   state action actions fallback backup value current))

(def stationary-policy-satisfies-optimality-equation-spec
  (let [value-function (function/arrow 'S nnrat)
        value-at (function/app 'value 'state)
        policy-backup
        (function/app 'backup 'value 'state (function/app 'policy 'state))
        optimum
        (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/nnrat-stationary-policy-satisfies-optimality-equation
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['policy (function/arrow 'S 'A)]
       ['value value-function]
       ['policy-fixed
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'value 'state)
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))))]
       ['greedy-consistent
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'value 'state)))]
       ['state 'S]]
      (equivalent value-at optimum))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['policy (function/arrow 'S 'A)]
       ['value value-function]
       ['policy-fixed
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'value 'state)
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))))]
       ['greedy-consistent
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'value 'state)))]
       ['state 'S]]
      (equivalent-transitive
       value-at policy-backup optimum
       (function/app 'policy-fixed 'state)
       (function/app 'greedy-consistent 'state)))}))

(def stationary-policy-value-is-optimal-given-uniqueness-spec
  (let [value-function (function/arrow 'S nnrat)
        optimum-at
        (fn [candidate state]
          (optimality-step 'S 'A 'actions 'fallback 'backup candidate state))
        optimality-fixed
        (fn [candidate]
          (function/forall
           [['state 'S]]
           (equivalent (optimum-at candidate 'state)
                       (function/app candidate 'state))))]
    {:name 'value/nnrat-stationary-policy-value-is-optimal-given-uniqueness
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['policy (function/arrow 'S 'A)]
       ['policy-value value-function]
       ['policy-value-fixed
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'policy-value 'state)
          (function/app 'backup 'policy-value 'state
                        (function/app 'policy 'state))))]
       ['greedy-consistent
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'backup 'policy-value 'state
                        (function/app 'policy 'state))
          (optimum-at 'policy-value 'state)))]
       ['optimal-value value-function]
       ['optimal-fixed (optimality-fixed 'optimal-value)]
       ['optimality-fixed-points-unique
        (function/forall
         [['left value-function]
          ['right value-function]
          ['left-fixed (optimality-fixed 'left)]
          ['right-fixed (optimality-fixed 'right)]
          ['state 'S]]
         (equivalent (function/app 'left 'state)
                     (function/app 'right 'state)))]
       ['state 'S]]
      (equivalent (function/app 'policy-value 'state)
                  (function/app 'optimal-value 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['policy (function/arrow 'S 'A)]
       ['policy-value value-function]
       ['policy-value-fixed
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'policy-value 'state)
          (function/app 'backup 'policy-value 'state
                        (function/app 'policy 'state))))]
       ['greedy-consistent
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'backup 'policy-value 'state
                        (function/app 'policy 'state))
          (optimum-at 'policy-value 'state)))]
       ['optimal-value value-function]
       ['optimal-fixed (optimality-fixed 'optimal-value)]
       ['optimality-fixed-points-unique
        (function/forall
         [['left value-function]
          ['right value-function]
          ['left-fixed (optimality-fixed 'left)]
          ['right-fixed (optimality-fixed 'right)]
          ['state 'S]]
         (equivalent (function/app 'left 'state)
                     (function/app 'right 'state)))]
       ['state 'S]]
      (let [policy-optimality-fixed
            (function/lam
             [['current 'S]]
             (let [policy-to-optimum
                   (function/app
                    (function/const*
                     'value/nnrat-stationary-policy-satisfies-optimality-equation
                     [U V])
                    'S 'A 'actions 'fallback 'backup 'policy 'policy-value
                    'policy-value-fixed 'greedy-consistent 'current)]
               (equivalent-symmetric
                (function/app 'policy-value 'current)
                (optimum-at 'policy-value 'current)
                policy-to-optimum)))]
        (function/app
         'optimality-fixed-points-unique
         'policy-value 'optimal-value
         policy-optimality-fixed 'optimal-fixed 'state)))}))

(def definition-specs [])
(def theorem-specs
  [stationary-policy-satisfies-optimality-equation-spec
   stationary-policy-value-is-optimal-given-uniqueness-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.greedy-optimal])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-policy-iteration-optimal theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.policy-iteration-optimal))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
