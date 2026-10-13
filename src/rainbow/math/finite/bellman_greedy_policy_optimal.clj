(ns rainbow.math.finite.bellman-greedy-policy-optimal
  "Fully concrete greedy-policy extraction for exact finite NNRAT Bellman models.

  The selected policy is the existing finite greedy action function at an
  optimal fixed value.  It is admissible, and any value satisfying its policy
  Bellman equation is pointwise equivalent to the optimal value.  The latter
  discharges the abstract fixed-policy uniqueness premise with the exact
  residual-based theorem.

  The combined theorem packages legality and value attainment as a constructive
  optimal-policy certificate.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-policy-residual-certificate
             :as policy-certificate]
            [rainbow.math.finite.greedy-optimal :as abstract-greedy]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

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
(defn- greedy-action
  [state action actions fallback backup value current]
  (app (function/const* 'value/nnrat-greedy-action [U V])
       state action actions fallback backup value current))
(defn- optimality-step
  [state action actions fallback backup value current]
  (app (function/const* 'value/nnrat-optimality-step [U V])
       state action actions fallback backup value current))

(defn- model-binders [backup selected]
  [['S type-u] ['A type-v]
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
   ['optimal-value (function/arrow 'S nnrat)]
   ['optimal-fixed-point
    (function/forall
     [['state 'S]]
     (req
      (optimality-step 'S 'A 'actions 'fallback backup
                       'optimal-value 'state)
      (app 'optimal-value 'state)))]
   ['policy-value (function/arrow 'S nnrat)]
   ['policy-value-fixed
    (function/forall
     [['state 'S]]
     (req (app backup 'policy-value 'state (app selected 'state))
          (app 'policy-value 'state)))]
   ['gap nnrat] ['inverse nnrat]
   ['discount-plus-gap-one
    (req (radd 'discount 'gap) nnrat-one)]
   ['inverse-times-gap-one
    (req (rmul 'inverse 'gap) nnrat-one)]])

(def model-arguments
  ['S 'A 'states 'actions 'transition 'reward 'discount
   'fallback 'fallback-admissible 'normalized 'state-covered
   'optimal-value 'optimal-fixed-point 'policy-value 'policy-value-fixed
   'gap 'inverse 'discount-plus-gap-one 'inverse-times-gap-one])

(def greedy-bellman-policy-admissible-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        selected
        (function/lam
         [['state 'S]]
         (greedy-action 'S 'A 'actions 'fallback backup
                        'optimal-value 'state))]
    {:name 'value/nnrat-greedy-bellman-policy-is-admissible
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
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
       ['optimal-value (function/arrow 'S nnrat)]]
      (function/forall
       [['state 'S]]
       (source-membership V 'A 'actions (app selected 'state))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
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
       ['optimal-value (function/arrow 'S nnrat)]]
      (function/lam
       [['state 'S]]
       (app
        (function/const* 'value/nnrat-greedy-action-is-admissible [U V])
        'S 'A 'actions 'fallback backup
        'fallback-admissible 'optimal-value 'state)))}))

(def greedy-bellman-policy-value-is-optimal-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        selected
        (function/lam
         [['state 'S]]
         (greedy-action 'S 'A 'actions 'fallback backup
                        'optimal-value 'state))
        binders (model-binders backup selected)]
    {:name 'value/nnrat-greedy-bellman-policy-value-is-optimal
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
             [['left (function/arrow 'S nnrat)]
              ['right (function/arrow 'S nnrat)]
              ['left-fixed
               (function/forall
                [['state 'S]]
                (req (app backup 'left 'state (app selected 'state))
                     (app 'left 'state)))]
              ['right-fixed
               (function/forall
                [['state 'S]]
                (req (app backup 'right 'state (app selected 'state))
                     (app 'right 'state)))]
              ['state 'S]]
             (app
              (function/const* 'bellman/nnrat-policy-fixed-points-unique
                               [U V])
              'S 'A 'states 'transition 'reward 'discount
              selected 'normalized 'state-covered
              'left 'left-fixed 'right 'right-fixed
              'gap 'inverse
              'discount-plus-gap-one 'inverse-times-gap-one
              'state))]
        (function/lam
         [['state 'S]]
         (app
          (function/const*
           'value/nnrat-greedy-policy-value-is-optimal-given-uniqueness
           [U V])
          'S 'A 'actions 'fallback backup
          'optimal-value 'optimal-fixed-point
          'policy-value 'policy-value-fixed
          fixed-points-unique 'state))))}))

(def greedy-bellman-policy-optimal-certificate-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        selected
        (function/lam
         [['state 'S]]
         (greedy-action 'S 'A 'actions 'fallback backup
                        'optimal-value 'state))
        binders (model-binders backup selected)
        admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app selected 'state)))
        attains
        (function/forall
         [['state 'S]]
         (req (app 'policy-value 'state) (app 'optimal-value 'state)))]
    {:name 'value/nnrat-greedy-bellman-policy-optimal-certificate
     :universes ['u 'v]
     :type
     (function/forall binders
                      (proposition/conjunction admissible attains))
     :value
     (function/lam
      binders
      (app
       (function/const* 'proposition/conjoin [])
       admissible attains
       (app
        (function/const*
         'value/nnrat-greedy-bellman-policy-is-admissible [U V])
        'S 'A 'states 'actions 'transition 'reward 'discount
        'fallback 'fallback-admissible 'optimal-value)
       (apply
        app
        (function/const*
         'value/nnrat-greedy-bellman-policy-value-is-optimal [U V])
        model-arguments)))}))

(def definition-specs [])
(def theorem-specs
  [greedy-bellman-policy-admissible-spec
   greedy-bellman-policy-value-is-optimal-spec
   greedy-bellman-policy-optimal-certificate-spec])

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
      policy-certificate/extend-environment
      (extend-specs-if-missing
       :finite-greedy-optimal abstract-greedy/theorem-specs)
      (support/extend-with
       :finite-bellman-greedy-policy-optimal theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
