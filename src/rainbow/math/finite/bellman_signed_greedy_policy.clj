(ns rainbow.math.finite.bellman-signed-greedy-policy
  "Greedy policy extraction from a signed Bellman fixed point.

  For the concrete Bellman model with ordinary nnrat transitions and arbitrary
  signed rewards/values, the runtime finite argmax defines a statewise policy.
  The policy is admissible whenever the fallback is admissible.  At an assumed
  Bellman fixed value, the backup selected by that policy is pointwise
  equivalent to the fixed value, because the signed optimality operator is
  definitionally the backup at its greedy action.

  This is a mathematical optimal-action certificate.  It does not construct a
  fixed point, verify a policy-evaluation executable, or connect to running
  Clojure code.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.bellman-signed-residual-certificate
             :as residual]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level])
       element source value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- greedy-action [state action actions fallback backup value current]
  (app (function/const* 'value/signed-greedy-action [U V])
       state action actions fallback backup value current))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))

(defn- model-objects []
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        backup
        (function/lam
         [['value value-function] ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward
              (from-nnrat 'discount) 'value 'state 'action))
        policy
        (function/lam
         [['state 'S]]
         (greedy-action
          'S 'A 'actions 'fallback backup 'fixed-value 'state))]
    {:value-function value-function :backup backup :policy policy}))

(def signed-greedy-policy-is-admissible-spec
  (let [{:keys [value-function backup policy]} (model-objects)]
    {:name 'value/nnrat-transition-signed-greedy-policy-is-admissible
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['fixed-value value-function]]
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (app policy 'state))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['fixed-value value-function]
       ['state 'S]]
      (app
       (function/const* 'value/signed-greedy-action-is-admissible [U V])
       'S 'A 'actions 'fallback backup
       'fallback-admissible 'fixed-value 'state))}))

(def signed-greedy-policy-attains-fixed-value-spec
  (let [{:keys [value-function backup policy]} (model-objects)
        step
        (fn [state]
          (optimality-step
           'S 'A 'actions 'fallback backup 'fixed-value state))]
    {:name 'value/nnrat-transition-signed-greedy-policy-attains-fixed-value
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (step 'state) (app 'fixed-value 'state)))]]
      (function/forall
       [['state 'S]]
       (veq (app backup 'fixed-value 'state (app policy 'state))
            (app 'fixed-value 'state))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (step 'state) (app 'fixed-value 'state)))]
       ['state 'S]]
      (app 'fixed-point 'state))}))

(def signed-greedy-fixed-point-policy-certificate-spec
  (let [{:keys [value-function backup policy]} (model-objects)
        admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app policy 'state)))
        attains
        (function/forall
         [['state 'S]]
         (veq (app backup 'fixed-value 'state (app policy 'state))
              (app 'fixed-value 'state)))
        step
        (fn [state]
          (optimality-step
           'S 'A 'actions 'fallback backup 'fixed-value state))]
    {:name 'value/nnrat-transition-signed-greedy-fixed-point-policy-certificate
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (step 'state) (app 'fixed-value 'state)))]]
      (proposition/conjunction admissible attains))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (step 'state) (app 'fixed-value 'state)))]]
      (app
       (function/const* 'proposition/conjoin [])
       admissible attains
       (app
        (function/const*
         'value/nnrat-transition-signed-greedy-policy-is-admissible [U V])
        'S 'A 'states 'actions 'transition 'reward 'discount
        'fallback 'fallback-admissible 'fixed-value)
       (app
        (function/const*
         'value/nnrat-transition-signed-greedy-policy-attains-fixed-value [U V])
        'S 'A 'states 'actions 'transition 'reward 'discount
        'fallback 'fixed-value 'fixed-point)))}))

(def definition-specs [])
(def theorem-specs
  [signed-greedy-policy-is-admissible-spec
   signed-greedy-policy-attains-fixed-value-spec
   signed-greedy-fixed-point-policy-certificate-spec])

(defn extend-environment [env]
  (-> env
      residual/extend-environment
      (support/extend-with
       :finite-bellman-signed-greedy-policy theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
