(ns rainbow.math.finite.greedy-optimal
  "Greedy policy extraction from a finite nnrat Bellman fixed point.

  The key proof transports the optimality fixed-point proposition across the
  opaque optimality-step unfold equality.  It never reduces greedy action or
  finite argmax.  The second theorem isolates the only remaining semantic
  ingredient: uniqueness of fixed points for the extracted policy operator.
  Native and axiom-free on D63."
  (:require [rainbow.math.finite.bellman-value-optimality
             :as bellman-value-optimality]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def V [:param 'v])
(def type-level [:succ [:zero]])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- rows-normalized [state action states transition]
  (function/app (function/const* 'markov/nnrat-rows-normalized [U V])
                state action states transition))

(defn- action-backup
  [state action states transition reward discount value current chosen]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount value current chosen))

(defn- greedy-action
  [state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-greedy-action [U V])
   state action actions fallback backup value current))

(defn- optimality-step
  [state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-optimality-step [U V])
   state action actions fallback backup value current))

(def greedy-policy-fixes-optimal-value-spec
  (let [value-function (function/arrow 'S nnrat)
        selected
        (greedy-action 'S 'A 'actions 'fallback 'backup
                       'optimal-value 'state)
        optimum
        (optimality-step 'S 'A 'actions 'fallback 'backup
                         'optimal-value 'state)
        policy-step (function/app 'backup 'optimal-value 'state selected)
        fixed-at (function/app 'optimal-value 'state)]
    {:name 'value/nnrat-greedy-policy-fixes-optimal-value
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['optimal-value value-function]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['state 'S]]
      (equivalent policy-step fixed-at))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['optimal-value value-function]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['state 'S]]
      (let [unfold
            (function/app
             (function/const* 'value/nnrat-optimality-step-unfold [U V])
             'S 'A 'actions 'fallback 'backup 'optimal-value 'state)]
        (function/app
         (function/const* 'equality/substitution [type-level])
         nnrat optimum policy-step unfold
         (function/lam [['candidate nnrat]]
                       (equivalent 'candidate fixed-at))
         (function/app 'optimal-fixed-point 'state))))}))

(def greedy-bellman-policy-fixes-optimal-value-spec
  (let [backup
        (function/app
         (function/const* 'bellman/nnrat-action-backup [U V])
         'S 'A 'states 'transition 'reward 'discount)
        selected
        (greedy-action 'S 'A 'actions 'fallback backup
                       'optimal-value 'state)]
    {:name 'value/nnrat-greedy-bellman-policy-fixes-optimal-value
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['optimal-value (function/arrow 'S nnrat)]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['state 'S]]
      (equivalent
       (action-backup 'S 'A 'states 'transition 'reward 'discount
                      'optimal-value 'state selected)
       (function/app 'optimal-value 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['optimal-value (function/arrow 'S nnrat)]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['state 'S]]
      (function/app
       (function/const*
        'value/nnrat-greedy-policy-fixes-optimal-value [U V])
       'S 'A 'actions 'fallback backup
       'optimal-value 'optimal-fixed-point 'state))}))

(def greedy-policy-value-is-optimal-given-uniqueness-spec
  (let [value-function (function/arrow 'S nnrat)
        selected
        (fn [state]
          (greedy-action 'S 'A 'actions 'fallback 'backup
                         'optimal-value state))
        policy-fixed
        (fn [value state]
          (equivalent
           (function/app 'backup value state (selected state))
           (function/app value state)))]
    {:name 'value/nnrat-greedy-policy-value-is-optimal-given-uniqueness
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['optimal-value value-function]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['policy-value value-function]
       ['policy-value-fixed
        (function/forall
         [['state 'S]]
         (policy-fixed 'policy-value 'state))]
       ['fixed-points-unique
        (function/forall
         [['left value-function]
          ['right value-function]
          ['left-fixed
           (function/forall
            [['state 'S]]
            (policy-fixed 'left 'state))]
          ['right-fixed
           (function/forall
            [['state 'S]]
            (policy-fixed 'right 'state))]
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
       ['optimal-value value-function]
       ['optimal-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (optimality-step 'S 'A 'actions 'fallback 'backup
                           'optimal-value 'state)
          (function/app 'optimal-value 'state)))]
       ['policy-value value-function]
       ['policy-value-fixed
        (function/forall
         [['state 'S]]
         (policy-fixed 'policy-value 'state))]
       ['fixed-points-unique
        (function/forall
         [['left value-function]
          ['right value-function]
          ['left-fixed
           (function/forall
            [['state 'S]]
            (policy-fixed 'left 'state))]
          ['right-fixed
           (function/forall
            [['state 'S]]
            (policy-fixed 'right 'state))]
          ['state 'S]]
         (equivalent (function/app 'left 'state)
                     (function/app 'right 'state)))]
       ['state 'S]]
      (let [optimal-policy-fixed
            (function/lam
             [['current 'S]]
             (function/app
              (function/const*
               'value/nnrat-greedy-policy-fixes-optimal-value [U V])
              'S 'A 'actions 'fallback 'backup
              'optimal-value 'optimal-fixed-point 'current))]
        (function/app
         'fixed-points-unique
         'policy-value 'optimal-value
         'policy-value-fixed optimal-policy-fixed 'state)))}))

(def definition-specs [])
(def theorem-specs
  [greedy-policy-fixes-optimal-value-spec
   greedy-bellman-policy-fixes-optimal-value-spec
   greedy-policy-value-is-optimal-given-uniqueness-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      bellman-value-optimality/extend-environment
      (support/extend-with :finite-greedy-optimal theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
