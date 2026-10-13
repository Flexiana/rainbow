(ns rainbow.math.finite.bellman-signed-optimal-contraction
  "Signed finite Bellman optimality inherits action-backup contraction.

  This composes the concrete signed reward/transition action backup with the
  runtime-length signed argmax operator.  Explicit nonnegative normalized
  transition rows and a nonnegative discount turn two-sided pointwise epsilon
  bounds into two-sided discount*epsilon bounds for the max-over-actions
  Bellman operator at every state.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-action-backup :as action-backup]
            [rainbow.math.finite.bellman-signed-optimality :as optimality]
            [rainbow.math.finite.signed-argmax :as finite-argmax]
            [rainbow.math.finite.signed-argmax-nonexpansive :as nonexpansive]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.minmax :as minmax]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- total-mass [element source mass]
  (app (function/const* 'probability/signed-total-mass [U])
       element source mass))
(defn- action-backup-at
  [state action states transition reward discount value current chosen]
  (app (function/const* 'bellman/signed-action-backup [U V])
       state action states transition reward discount value current chosen))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))

(def optimality-step-additively-contractive-spec
  (let [backup
        (function/lam
         [['value (function/arrow 'S signed)]
          ['state 'S] ['action 'A]]
         (action-backup-at
          'S 'A 'states 'transition 'reward 'discount
          'value 'state 'action))
        contracted-epsilon (multiply 'discount 'epsilon)]
    {:name 'value/signed-optimality-step-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed]
       ['discount-nonnegative (at-most signed-zero 'discount)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['transition-nonnegative
        (function/forall
         [['state 'S] ['action 'A] ['next-state 'S]]
         (at-most signed-zero
                  (app 'transition 'state 'action 'next-state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (equivalent
          (total-mass 'S 'states (app 'transition 'state 'action))
          signed-one))]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (at-most (app 'left-value 'state)
                  (add (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (at-most (app 'right-value 'state)
                  (add (app 'left-value 'state) 'epsilon)))]]
      (function/forall
       [['state 'S]]
       (let [left-step
             (optimality-step
              'S 'A 'actions 'fallback backup 'left-value 'state)
             right-step
             (optimality-step
              'S 'A 'actions 'fallback backup 'right-value 'state)]
         (proposition/conjunction
          (at-most left-step (add right-step contracted-epsilon))
          (at-most right-step (add left-step contracted-epsilon))))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed]
       ['discount-nonnegative (at-most signed-zero 'discount)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['transition-nonnegative
        (function/forall
         [['state 'S] ['action 'A] ['next-state 'S]]
         (at-most signed-zero
                  (app 'transition 'state 'action 'next-state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (equivalent
          (total-mass 'S 'states (app 'transition 'state 'action))
          signed-one))]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (at-most (app 'left-value 'state)
                  (add (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (at-most (app 'right-value 'state)
                  (add (app 'left-value 'state) 'epsilon)))]]
      (function/lam
       [['state 'S]]
       (let [left-action-pointwise
             (function/lam
              [['action 'A]
               ['member (source-membership V 'A 'actions 'action)]]
              (app
               (function/const*
                'bellman/signed-action-backup-additive-upper-bound [U V])
               'S 'A 'states 'transition 'reward
               'discount 'discount-nonnegative
               'left-value 'right-value 'epsilon 'left-pointwise
               'state 'action
               (app 'transition-nonnegative 'state 'action)
               (app 'normalized 'state 'action)))
             right-action-pointwise
             (function/lam
              [['action 'A]
               ['member (source-membership V 'A 'actions 'action)]]
              (app
               (function/const*
                'bellman/signed-action-backup-additive-upper-bound [U V])
               'S 'A 'states 'transition 'reward
               'discount 'discount-nonnegative
               'right-value 'left-value 'epsilon 'right-pointwise
               'state 'action
               (app 'transition-nonnegative 'state 'action)
               (app 'normalized 'state 'action)))]
         (app
          (function/const*
           'value/signed-optimality-step-additively-nonexpansive [U V])
          'S 'A 'actions 'fallback 'fallback-admissible backup
          'left-value 'right-value contracted-epsilon 'state
          left-action-pointwise right-action-pointwise))))}))

(def definition-specs [])
(def theorem-specs [optimality-step-additively-contractive-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(defn extend-environment [env]
  (-> env
      action-backup/extend-environment
      (extend-specs-if-missing
       :signed-decide-order
       (concat decide/definition-specs decide/theorem-specs))
      (extend-specs-if-missing
       :signed-minmax
       (concat minmax/definition-specs minmax/theorem-specs))
      (extend-specs-if-missing
       :finite-signed-argmax
       (concat finite-argmax/definition-specs finite-argmax/theorem-specs))
      (extend-specs-if-missing
       :finite-signed-argmax-nonexpansive nonexpansive/theorem-specs)
      (extend-specs-if-missing
       :finite-bellman-signed-optimality
       (concat optimality/definition-specs optimality/theorem-specs))
      (support/extend-with
       :finite-bellman-signed-optimal-contraction theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
