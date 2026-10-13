(ns rainbow.math.finite.bellman-signed-policy-optimal
  "Concrete signed greedy-policy optimality for finite Bellman models.

  Ordinary normalized nnrat transition rows are embedded into signed rationals.
  For any fixed state-to-action policy, the resulting signed action-backup
  operator is additively contractive.  The finite signed sup metric and exact
  inverse-gap certificate therefore make its fixed point unique.  Applying
  that result to the finite signed argmax policy proves that any separately
  supplied fixed-policy value is pointwise equivalent to the assumed Bellman
  optimal fixed value.

  Fixed-point existence and executable policy evaluation remain premises or
  open implementation obligations.  Native, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-fixed-point-uniqueness
             :as uniqueness]
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
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level])
       element source value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- finite-distance [element source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [U])
       element source left right))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- greedy-action [state action actions fallback backup value current]
  (app (function/const* 'value/signed-greedy-action [U V])
       state action actions fallback backup value current))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime same-left same-right ordered))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))

(defn- model-objects [policy]
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        rate (from-nnrat 'discount)
        backup
        (function/lam
         [['value value-function] ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward rate
              'value 'state 'action))
        operator
        (function/lam
         [['value value-function]]
         (function/lam
          [['state 'S]]
          (app backup 'value 'state (app policy 'state))))]
    {:value-function value-function
     :embedded-transition embedded-transition
     :rate rate
     :backup backup
     :operator operator}))

(def signed-policy-step-additively-contractive-spec
  (let [{:keys [value-function embedded-transition rate backup operator]}
        (model-objects 'policy)
        close
        (fn [left right epsilon]
          (proposition/conjunction
           (sle left (sadd right epsilon))
           (sle right (sadd left epsilon))))]
    {:name 'value/nnrat-transition-signed-policy-step-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              nnrat-one))]
       ['policy (function/arrow 'S 'A)]
       ['left-value value-function]
       ['right-value value-function]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (sle (app 'left-value 'state)
              (sadd (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (sle (app 'right-value 'state)
              (sadd (app 'left-value 'state) 'epsilon)))]]
      (function/forall
       [['state 'S]]
       (close (app operator 'left-value 'state)
              (app operator 'right-value 'state)
              (smul rate 'epsilon))))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              nnrat-one))]
       ['policy (function/arrow 'S 'A)]
       ['left-value value-function]
       ['right-value value-function]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (sle (app 'left-value 'state)
              (sadd (app 'right-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (sle (app 'right-value 'state)
              (sadd (app 'left-value 'state) 'epsilon)))]
       ['state 'S]]
      (app
       (function/const* 'bellman/signed-action-backup-additively-contractive
                        [U V])
       'S 'A 'states embedded-transition 'reward rate
       (app (function/const* 'signed/zero-at-most-from-nnrat []) 'discount)
       'left-value 'right-value 'epsilon
       'left-pointwise 'right-pointwise
       'state (app 'policy 'state)
       (function/lam
        [['next-state 'S]]
        (app (function/const* 'signed/zero-at-most-from-nnrat [])
             (app 'transition 'state (app 'policy 'state) 'next-state)))
       (app
        (function/const* 'probability/signed-total-mass-normalized-from-nnrat
                         [U])
        'S 'states (app 'transition 'state (app 'policy 'state))
       (app 'normalized 'state (app 'policy 'state)))))}))

(defn- policy-residual-binders [value-function operator]
  [['S type-u] ['A type-v]
   ['states (exact-finset-of U 'S)]
   ['state-covered
    (function/forall
     [['state 'S]]
     (source-membership U 'S 'states 'state))]
   ['transition (function/arrow 'S 'A 'S nnrat)]
   ['reward (function/arrow 'S 'A signed)]
   ['discount nnrat]
   ['normalized
    (function/forall
     [['state 'S] ['action 'A]]
     (req (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
   ['policy (function/arrow 'S 'A)]
   ['fixed-value value-function]
   ['fixed-point
    (function/forall
     [['state 'S]]
     (veq (app operator 'fixed-value 'state)
          (app 'fixed-value 'state)))]
   ['candidate value-function]])

(def signed-policy-fixed-point-self-bound-spec
  (let [{:keys [value-function rate operator]} (model-objects 'policy)
        distance (finite-distance 'S 'states 'candidate 'fixed-value)
        residual (finite-distance
                  'S 'states 'candidate (app operator 'candidate))]
    {:name 'value/nnrat-transition-signed-policy-fixed-point-sup-distance-self-bound
     :universes ['u 'v]
     :type
     (function/forall
      (policy-residual-binders value-function operator)
      (sle distance (sadd residual (smul rate distance))))
     :value
     (function/lam
      (policy-residual-binders value-function operator)
      (app
       (function/const*
        'metric/finite-signed-sup-distance-self-bound-of-additive-contraction
        [U])
       'S 'states 'state-covered operator rate
       (app (function/const* 'signed/zero-at-most-from-nnrat []) 'discount)
       (function/lam
        [['left-value value-function]
         ['right-value value-function]
         ['epsilon signed]
         ['left-pointwise
          (function/forall
           [['state 'S]]
           (sle (app 'left-value 'state)
                (sadd (app 'right-value 'state) 'epsilon)))]
         ['right-pointwise
          (function/forall
           [['state 'S]]
           (sle (app 'right-value 'state)
                (sadd (app 'left-value 'state) 'epsilon)))]
         ['state 'S]]
        (app
         (function/const*
          'value/nnrat-transition-signed-policy-step-additively-contractive
          [U V])
         'S 'A 'states 'transition 'reward 'discount 'normalized 'policy
         'left-value 'right-value 'epsilon
         'left-pointwise 'right-pointwise 'state))
       'fixed-value 'fixed-point 'candidate))}))

(def signed-policy-fixed-point-residual-bound-spec
  (let [{:keys [value-function rate operator]} (model-objects 'policy)
        distance (finite-distance 'S 'states 'candidate 'fixed-value)
        residual (finite-distance
                  'S 'states 'candidate (app operator 'candidate))
        binders
        (concat
         (policy-residual-binders value-function operator)
         [['gap signed] ['inverse signed]
          ['inverse-nonnegative (sle signed-zero 'inverse)]
          ['discount-plus-gap-one (veq (sadd rate 'gap) signed-one)]
          ['inverse-times-gap-one (veq (smul 'inverse 'gap) signed-one)]])]
    {:name 'value/nnrat-transition-signed-policy-fixed-point-residual-bound
     :universes ['u 'v]
     :type
     (function/forall binders
                      (sle distance (smul 'inverse residual)))
     :value
     (function/lam
      binders
      (app
       (function/const* 'signed/inverse-gap-residual-bound [])
       distance residual rate 'gap 'inverse
       'inverse-nonnegative
       'discount-plus-gap-one 'inverse-times-gap-one
       (app
        (function/const*
         'value/nnrat-transition-signed-policy-fixed-point-sup-distance-self-bound
         [U V])
        'S 'A 'states 'state-covered 'transition 'reward 'discount
        'normalized 'policy 'fixed-value 'fixed-point 'candidate)))}))

(def signed-policy-fixed-point-stopping-certificate-spec
  (let [{:keys [value-function rate operator]} (model-objects 'policy)
        distance (finite-distance 'S 'states 'candidate 'fixed-value)
        residual (finite-distance
                  'S 'states 'candidate (app operator 'candidate))
        base-binders
        (concat
         (policy-residual-binders value-function operator)
         [['gap signed] ['inverse signed]
          ['inverse-nonnegative (sle signed-zero 'inverse)]
          ['discount-plus-gap-one (veq (sadd rate 'gap) signed-one)]
          ['inverse-times-gap-one (veq (smul 'inverse 'gap) signed-one)]])
        binders
        (concat
         base-binders
         [['threshold signed]
          ['residual-at-most-threshold (sle residual 'threshold)]])]
    {:name 'value/nnrat-transition-signed-policy-fixed-point-stopping-certificate
     :universes ['u 'v]
     :type
     (function/forall binders
                      (sle distance (smul 'inverse 'threshold)))
     :value
     (function/lam
      binders
      (let [certified
            (app
             (function/const*
              'value/nnrat-transition-signed-policy-fixed-point-residual-bound
              [U V])
             'S 'A 'states 'state-covered 'transition 'reward 'discount
             'normalized 'policy 'fixed-value 'fixed-point 'candidate
             'gap 'inverse 'inverse-nonnegative
             'discount-plus-gap-one 'inverse-times-gap-one)
            scaled-threshold
            (app (function/const* 'signed/multiply-left-monotone [])
                 'inverse residual 'threshold
                 'inverse-nonnegative 'residual-at-most-threshold)]
        (order-transitive
         distance (smul 'inverse residual) (smul 'inverse 'threshold)
         certified scaled-threshold)))}))

(def signed-policy-fixed-points-unique-spec
  (let [{:keys [value-function rate operator]} (model-objects 'policy)
        distance (finite-distance 'S 'states 'left 'right)
        residual (finite-distance 'S 'states 'left (app operator 'left))
        scaled-residual (smul 'inverse residual)
        binders
        [['S type-u] ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['state-covered
          (function/forall
           [['state 'S]]
           (source-membership U 'S 'states 'state))]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A signed)]
         ['discount nnrat]
         ['normalized
          (function/forall
           [['state 'S] ['action 'A]]
           (req (nnrat-total-mass
                 'S 'states (app 'transition 'state 'action))
                nnrat-one))]
         ['policy (function/arrow 'S 'A)]
         ['left value-function]
         ['left-fixed
          (function/forall
           [['state 'S]]
           (veq (app operator 'left 'state) (app 'left 'state)))]
         ['right value-function]
         ['right-fixed
          (function/forall
           [['state 'S]]
           (veq (app operator 'right 'state) (app 'right 'state)))]
         ['gap signed] ['inverse signed]
         ['inverse-nonnegative (sle signed-zero 'inverse)]
         ['discount-plus-gap-one (veq (sadd rate 'gap) signed-one)]
         ['inverse-times-gap-one (veq (smul 'inverse 'gap) signed-one)]]]
    {:name 'value/nnrat-transition-signed-policy-fixed-points-unique
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (veq (app 'left 'state) (app 'right 'state))))
     :value
     (function/lam
      binders
      (let [contractive
            (function/lam
             [['left-value value-function]
              ['right-value value-function]
              ['epsilon signed]
              ['left-pointwise
               (function/forall
                [['state 'S]]
                (sle (app 'left-value 'state)
                     (sadd (app 'right-value 'state) 'epsilon)))]
              ['right-pointwise
               (function/forall
                [['state 'S]]
                (sle (app 'right-value 'state)
                     (sadd (app 'left-value 'state) 'epsilon)))]
              ['state 'S]]
             (app
              (function/const*
               'value/nnrat-transition-signed-policy-step-additively-contractive
               [U V])
              'S 'A 'states 'transition 'reward 'discount 'normalized 'policy
              'left-value 'right-value 'epsilon
              'left-pointwise 'right-pointwise 'state))
            residual-zero
            (app
             (function/const*
              'metric/finite-signed-sup-distance-zero-of-pointwise-equivalent
              [U])
             'S 'states 'left (app operator 'left)
             (function/lam
              [['state 'S]
               ['member (source-membership U 'S 'states 'state)]]
              (equivalent-symmetric
               (app operator 'left 'state) (app 'left 'state)
               (app 'left-fixed 'state))))
            self-bound
            (app
             (function/const*
              'metric/finite-signed-sup-distance-self-bound-of-additive-contraction
              [U])
             'S 'states 'state-covered operator rate
             (app (function/const* 'signed/zero-at-most-from-nnrat [])
                  'discount)
             contractive 'right 'right-fixed 'left)
            residual-bound
            (app
             (function/const* 'signed/inverse-gap-residual-bound [])
             distance residual rate 'gap 'inverse
             'inverse-nonnegative
             'discount-plus-gap-one 'inverse-times-gap-one self-bound)
            scaled-zero
            (equivalent-transitive
             scaled-residual (smul 'inverse signed-zero) signed-zero
             (app
              (function/const* 'signed/multiply-left-respects-equivalence [])
              residual signed-zero 'inverse residual-zero)
             (app (function/const* 'signed/multiply-zero-right []) 'inverse))
            distance-at-most-zero
            (order-respects
             distance distance scaled-residual signed-zero
             (equivalent-reflexive distance) scaled-zero residual-bound)
            zero-at-most-distance
            (app
             (function/const*
              'metric/finite-signed-sup-distance-nonnegative [U])
             'S 'states 'left 'right)
            distance-zero
            (antisymmetric distance signed-zero
                           distance-at-most-zero zero-at-most-distance)
            memberwise
            (app
             (function/const*
              'metric/pointwise-equivalent-of-finite-signed-sup-distance-zero
              [U])
             'S 'states 'left 'right distance-zero)]
        (function/lam
         [['state 'S]]
         (app memberwise 'state (app 'state-covered 'state)))))}))

(defn- greedy-model []
  (let [{:keys [value-function backup]} (model-objects 'unused-policy)
        selected
        (function/lam
         [['state 'S]]
         (greedy-action 'S 'A 'actions 'fallback backup
                        'optimal-value 'state))
        operator (:operator (model-objects selected))
        optimality
        (function/lam
         [['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step 'S 'A 'actions 'fallback backup
                           'value 'state)))]
    {:value-function value-function
     :backup backup
     :selected selected
     :operator operator
     :optimality optimality}))

(defn- greedy-model-binders [operator optimality]
  [['S type-u] ['A type-v]
   ['states (exact-finset-of U 'S)]
   ['state-covered
    (function/forall
     [['state 'S]]
     (source-membership U 'S 'states 'state))]
   ['actions (exact-finset-of V 'A)]
   ['transition (function/arrow 'S 'A 'S nnrat)]
   ['reward (function/arrow 'S 'A signed)]
   ['discount nnrat]
   ['fallback (function/arrow 'S 'A)]
   ['fallback-admissible
    (function/forall
     [['state 'S]]
     (source-membership V 'A 'actions (app 'fallback 'state)))]
   ['normalized
    (function/forall
     [['state 'S] ['action 'A]]
     (req (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
   ['optimal-value (function/arrow 'S signed)]
   ['optimal-fixed
    (function/forall
     [['state 'S]]
     (veq (app optimality 'optimal-value 'state)
          (app 'optimal-value 'state)))]
   ['policy-value (function/arrow 'S signed)]
   ['policy-value-fixed
    (function/forall
     [['state 'S]]
     (veq (app operator 'policy-value 'state)
          (app 'policy-value 'state)))]
   ['gap signed] ['inverse signed]
   ['inverse-nonnegative (sle signed-zero 'inverse)]
   ['discount-plus-gap-one
    (veq (sadd (from-nnrat 'discount) 'gap) signed-one)]
   ['inverse-times-gap-one
    (veq (smul 'inverse 'gap) signed-one)]])

(def signed-greedy-policy-value-is-optimal-spec
  (let [{:keys [value-function backup selected operator optimality]}
        (greedy-model)
        binders (greedy-model-binders operator optimality)]
    {:name 'value/nnrat-transition-signed-greedy-policy-value-is-optimal
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (veq (app 'policy-value 'state)
            (app 'optimal-value 'state))))
     :value
     (function/lam
      binders
      (let [optimal-policy-fixed
            (function/lam
             [['state 'S]]
             (app
              (function/const*
               'value/nnrat-transition-signed-greedy-policy-attains-fixed-value
               [U V])
              'S 'A 'states 'actions 'transition 'reward 'discount
              'fallback 'optimal-value 'optimal-fixed 'state))]
        (app
         (function/const*
          'value/nnrat-transition-signed-policy-fixed-points-unique [U V])
         'S 'A 'states 'state-covered
         'transition 'reward 'discount 'normalized selected
         'policy-value 'policy-value-fixed
         'optimal-value optimal-policy-fixed
         'gap 'inverse 'inverse-nonnegative
         'discount-plus-gap-one 'inverse-times-gap-one)))}))

(def signed-greedy-policy-optimal-certificate-spec
  (let [{:keys [backup selected operator optimality]} (greedy-model)
        binders (greedy-model-binders operator optimality)
        admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app selected 'state)))
        optimal
        (function/forall
         [['state 'S]]
         (veq (app 'policy-value 'state)
              (app 'optimal-value 'state)))]
    {:name 'value/nnrat-transition-signed-greedy-policy-optimal-certificate
     :universes ['u 'v]
     :type
     (function/forall binders (proposition/conjunction admissible optimal))
     :value
     (function/lam
      binders
      (app
       (function/const* 'proposition/conjoin [])
       admissible optimal
       (app
        (function/const*
         'value/nnrat-transition-signed-greedy-policy-is-admissible [U V])
        'S 'A 'states 'actions 'transition 'reward 'discount
        'fallback 'fallback-admissible 'optimal-value)
       (app
        (function/const*
         'value/nnrat-transition-signed-greedy-policy-value-is-optimal [U V])
        'S 'A 'states 'state-covered 'actions
        'transition 'reward 'discount 'fallback 'fallback-admissible
        'normalized 'optimal-value 'optimal-fixed
        'policy-value 'policy-value-fixed
        'gap 'inverse 'inverse-nonnegative
        'discount-plus-gap-one 'inverse-times-gap-one)))}))

(def signed-stationary-policy-value-is-optimal-spec
  (let [{:keys [value-function backup]} (model-objects 'policy)
        policy-backup
        (fn [value state]
          (app backup value state (app 'policy state)))
        optimality
        (fn [value state]
          (optimality-step 'S 'A 'actions 'fallback backup value state))
        binders
        [['S type-u] ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['state-covered
          (function/forall
           [['state 'S]]
           (source-membership U 'S 'states 'state))]
         ['actions (exact-finset-of V 'A)]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A signed)]
         ['discount nnrat]
         ['fallback (function/arrow 'S 'A)]
         ['fallback-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'fallback 'state)))]
         ['normalized
          (function/forall
           [['state 'S] ['action 'A]]
           (req (nnrat-total-mass
                 'S 'states (app 'transition 'state 'action))
                nnrat-one))]
         ['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'policy 'state)))]
         ['policy-value value-function]
         ['policy-value-fixed
          (function/forall
           [['state 'S]]
           (veq (policy-backup 'policy-value 'state)
                (app 'policy-value 'state)))]
         ['greedy-consistent
          (function/forall
           [['state 'S]]
           (veq (policy-backup 'policy-value 'state)
                (optimality 'policy-value 'state)))]
         ['optimal-value value-function]
         ['optimal-fixed
          (function/forall
           [['state 'S]]
           (veq (optimality 'optimal-value 'state)
                (app 'optimal-value 'state)))]
         ['gap signed] ['inverse signed]
         ['inverse-nonnegative (sle signed-zero 'inverse)]
         ['discount-plus-gap-one
          (veq (sadd (from-nnrat 'discount) 'gap) signed-one)]
         ['inverse-times-gap-one
          (veq (smul 'inverse 'gap) signed-one)]]]
    {:name 'value/nnrat-transition-signed-stationary-policy-value-is-optimal
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (veq (app 'policy-value 'state)
            (app 'optimal-value 'state))))
     :value
     (function/lam
      binders
      (let [policy-is-optimality-fixed
            (function/lam
             [['state 'S]]
             (equivalent-transitive
              (optimality 'policy-value 'state)
              (policy-backup 'policy-value 'state)
              (app 'policy-value 'state)
              (equivalent-symmetric
               (policy-backup 'policy-value 'state)
               (optimality 'policy-value 'state)
               (app 'greedy-consistent 'state))
              (app 'policy-value-fixed 'state)))]
        (app
         (function/const*
          'value/nnrat-transition-signed-optimality-fixed-points-unique
          [U V])
         'S 'A 'states 'state-covered 'actions
         'transition 'reward 'discount
         'fallback 'fallback-admissible 'normalized
         'policy-value policy-is-optimality-fixed
         'optimal-value 'optimal-fixed
         'gap 'inverse 'inverse-nonnegative
         'discount-plus-gap-one 'inverse-times-gap-one)))}))

(def definition-specs [])
(def theorem-specs
  [signed-policy-step-additively-contractive-spec
   signed-policy-fixed-point-self-bound-spec
   signed-policy-fixed-point-residual-bound-spec
   signed-policy-fixed-point-stopping-certificate-spec
   signed-policy-fixed-points-unique-spec
   signed-greedy-policy-value-is-optimal-spec
   signed-greedy-policy-optimal-certificate-spec
   signed-stationary-policy-value-is-optimal-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(defn extend-environment [env]
  (-> env
      uniqueness/extend-environment
      (support/extend-with
       :finite-bellman-signed-policy-optimal theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
