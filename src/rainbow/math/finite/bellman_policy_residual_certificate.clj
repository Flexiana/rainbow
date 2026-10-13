(ns rainbow.math.finite.bellman-policy-residual-certificate
  "Residual certificates and uniqueness for exact finite fixed-policy Bellman operators.

  The module first factors the metric argument into a reusable contracted-image
  theorem.  It then instantiates action-backup contraction at `policy state`,
  obtaining the same sharp inverse-gap residual and stopping certificates as
  for Bellman optimality.  Zero residual plus metric separation yields
  pointwise uniqueness of fixed-policy values.

  `state-covered` remains explicit whenever a finite radius must supply a
  carrier-wide contraction premise.  Native, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-residual-certificate
             :as optimality-certificate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.metric-separation :as separation]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level])
       element source value))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- finite-radius [state source left right]
  (app (function/const* 'metric/finite-nnrat-sup-radius [U])
       state source left right))
(defn- rows-normalized [state action states transition]
  (app (function/const* 'markov/nnrat-rows-normalized [U V])
       state action states transition))
(defn- backup-operator
  [state action states transition reward discount]
  (app (function/const* 'bellman/nnrat-action-backup [U V])
       state action states transition reward discount))
(defn- policy-step [backup policy value state]
  (app backup value state (app policy state)))
(defn- close [left right epsilon]
  (proposition/conjunction
   (rle left (radd right epsilon))
   (rle right (radd left epsilon))))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- add-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left equivalent-left right equivalent-right same-left same-right))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'nnrat/equivalent-to-at-most [])
       left right same))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- order-respects
  [left equivalent-left right equivalent-right
   same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left equivalent-left right equivalent-right
       same-left same-right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'nnrat/at-most-antisymmetric [])
       left right left-right right-left))
(defn- additive-closeness [left right epsilon bounded]
  (app (function/const* 'nnrat/additive-closeness-of-distance-at-most [])
       left right epsilon bounded))
(defn- distance-of-closeness
  [left right epsilon left-close right-close]
  (app (function/const* 'nnrat/distance-at-most-of-additive-closeness [])
       left right epsilon left-close right-close))
(defn- radius-upper-bound [state source left right current member]
  (app (function/const* 'metric/finite-nnrat-sup-radius-upper-bound [U])
       state source left right current member))

(def contracted-image-self-bound-spec
  (let [value-function (function/arrow 'A nnrat)
        fixed-radius (finite-radius 'A 'source 'candidate 'fixed-value)
        residual-radius (finite-radius 'A 'source 'candidate 'image)
        contracted-radius (rmul 'rate fixed-radius)
        self-upper (radd residual-radius contracted-radius)]
    {:name 'metric/finite-nnrat-sup-radius-self-bound-of-contracted-image
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['source (exact-finset-of U 'A)]
       ['candidate value-function]
       ['image value-function]
       ['fixed-value value-function]
       ['rate nnrat]
       ['contracted-pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership U 'A 'source 'state)]]
         (close (app 'image 'state)
                (app 'fixed-value 'state)
                contracted-radius))]]
      (rle fixed-radius self-upper))
     :value
     (function/lam
      [['A type-u]
       ['source (exact-finset-of U 'A)]
       ['candidate value-function]
       ['image value-function]
       ['fixed-value value-function]
       ['rate nnrat]
       ['contracted-pointwise
        (function/forall
         [['state 'A]
          ['member (source-membership U 'A 'source 'state)]]
         (close (app 'image 'state)
                (app 'fixed-value 'state)
                contracted-radius))]]
      (app
       (function/const* 'metric/finite-nnrat-sup-radius-bounded [U])
       'A 'source 'candidate 'fixed-value self-upper
       (app (function/const* 'nnrat/zero-at-most []) self-upper)
       (function/lam
        [['state 'A]
         ['member (source-membership U 'A 'source 'state)]]
        (let [candidate-at (app 'candidate 'state)
              image-at (app 'image 'state)
              fixed-at (app 'fixed-value 'state)
              residual-close
              (additive-closeness
               candidate-at image-at residual-radius
               (radius-upper-bound
                'A 'source 'candidate 'image 'state 'member))
              candidate-image
              (left-conjunct
               (rle candidate-at (radd image-at residual-radius))
               (rle image-at (radd candidate-at residual-radius))
               residual-close)
              image-candidate
              (right-conjunct
               (rle candidate-at (radd image-at residual-radius))
               (rle image-at (radd candidate-at residual-radius))
               residual-close)
              contracted-close (app 'contracted-pointwise 'state 'member)
              image-fixed
              (left-conjunct
               (rle image-at (radd fixed-at contracted-radius))
               (rle fixed-at (radd image-at contracted-radius))
               contracted-close)
              fixed-image
              (right-conjunct
               (rle image-at (radd fixed-at contracted-radius))
               (rle fixed-at (radd image-at contracted-radius))
               contracted-close)
              candidate-fixed
              (app (function/const* 'nnrat/additive-upper-triangle [])
                   candidate-at image-at fixed-at
                   residual-radius contracted-radius
                   candidate-image image-fixed)
              reverse-upper
              (radd candidate-at
                    (radd contracted-radius residual-radius))
              fixed-candidate-reversed
              (app (function/const* 'nnrat/additive-upper-triangle [])
                   fixed-at image-at candidate-at
                   contracted-radius residual-radius
                   fixed-image image-candidate)
              fixed-candidate
              (order-respects
               fixed-at fixed-at
               (radd candidate-at self-upper) reverse-upper
               (equivalent-reflexive fixed-at)
               (app
                (function/const* 'nnrat/add-respects-equivalence [])
                candidate-at candidate-at
                self-upper (radd contracted-radius residual-radius)
                (equivalent-reflexive candidate-at)
                (app (function/const* 'nnrat/add-commutative [])
                     residual-radius contracted-radius))
               fixed-candidate-reversed)]
          (distance-of-closeness
           candidate-at fixed-at self-upper
           candidate-fixed fixed-candidate)))))}))

(def policy-step-fixed-point-contraction-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        left-step (policy-step backup 'policy 'left-value 'state)
        fixed-step (policy-step backup 'policy 'fixed-value 'state)
        fixed-at (app 'fixed-value 'state)
        contracted (rmul 'discount 'epsilon)
        step-left (rle left-step (radd fixed-step contracted))
        step-right (rle fixed-step (radd left-step contracted))]
    {:name 'bellman/nnrat-policy-step-fixed-point-contraction
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['fixed-value (function/arrow 'S nnrat)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (req (policy-step backup 'policy 'fixed-value 'state)
              (app 'fixed-value 'state)))]
       ['left-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (rle (app 'left-value 'state)
              (radd (app 'fixed-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (rle (app 'fixed-value 'state)
              (radd (app 'left-value 'state) 'epsilon)))]
       ['state 'S]]
      (close left-step fixed-at contracted))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['fixed-value (function/arrow 'S nnrat)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (req (policy-step backup 'policy 'fixed-value 'state)
              (app 'fixed-value 'state)))]
       ['left-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['state 'S]]
         (rle (app 'left-value 'state)
              (radd (app 'fixed-value 'state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['state 'S]]
         (rle (app 'fixed-value 'state)
              (radd (app 'left-value 'state) 'epsilon)))]
       ['state 'S]]
      (let [raw
            (app
             (function/const* 'bellman/nnrat-action-backup-contraction [U V])
             'S 'A 'states 'transition 'reward 'discount
             'left-value 'fixed-value 'epsilon
             'left-pointwise 'right-pointwise
             'state (app 'policy 'state)
             (app 'normalized 'state (app 'policy 'state)))
            fixed-is-step
            (equivalent-symmetric
             fixed-step fixed-at (app 'fixed-point 'state))
            fixed-sum-is-step-sum
            (add-respects
             fixed-at fixed-step contracted contracted
             fixed-is-step (equivalent-reflexive contracted))
            result-left
            (order-respects
             left-step left-step
             (radd fixed-at contracted) (radd fixed-step contracted)
             (equivalent-reflexive left-step) fixed-sum-is-step-sum
             (left-conjunct step-left step-right raw))
            result-right
            (order-respects
             fixed-at fixed-step
             (radd left-step contracted) (radd left-step contracted)
             fixed-is-step (equivalent-reflexive (radd left-step contracted))
             (right-conjunct step-left step-right raw))]
        (app (function/const* 'proposition/conjoin [])
             (rle left-step (radd fixed-at contracted))
             (rle fixed-at (radd left-step contracted))
             result-left result-right)))}))

(defn- policy-model-binders [backup]
  [['S type-u] ['A type-v]
   ['states (exact-finset-of U 'S)]
   ['transition (function/arrow 'S 'A 'S nnrat)]
   ['reward (function/arrow 'S 'A nnrat)]
   ['discount nnrat]
   ['policy (function/arrow 'S 'A)]
   ['normalized (rows-normalized 'S 'A 'states 'transition)]
   ['state-covered
    (function/forall
     [['state 'S]]
     (source-membership U 'S 'states 'state))]
   ['fixed-value (function/arrow 'S nnrat)]
   ['fixed-point
    (function/forall
     [['state 'S]]
     (req (policy-step backup 'policy 'fixed-value 'state)
          (app 'fixed-value 'state)))]])

(def policy-model-arguments
  ['S 'A 'states 'transition 'reward 'discount 'policy
   'normalized 'state-covered 'fixed-value 'fixed-point])

(def policy-fixed-point-self-bound-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        image
        (function/lam
         [['state 'S]]
         (policy-step backup 'policy 'candidate 'state))
        fixed-radius (finite-radius 'S 'states 'candidate 'fixed-value)
        residual (finite-radius 'S 'states 'candidate image)]
    {:name 'bellman/nnrat-policy-fixed-point-sup-radius-self-bound
     :universes ['u 'v]
     :type
     (function/forall
      (concat (policy-model-binders backup)
              [['candidate value-function]])
      (rle fixed-radius
           (radd residual (rmul 'discount fixed-radius))))
     :value
     (function/lam
      (concat (policy-model-binders backup)
              [['candidate value-function]])
      (let [candidate-fixed-close
            (function/lam
             [['current 'S]]
             (additive-closeness
              (app 'candidate 'current)
              (app 'fixed-value 'current)
              fixed-radius
              (radius-upper-bound
               'S 'states 'candidate 'fixed-value 'current
               (app 'state-covered 'current))))
            left-pointwise
            (function/lam
             [['current 'S]]
             (let [left
                   (rle (app 'candidate 'current)
                        (radd (app 'fixed-value 'current) fixed-radius))
                   right
                   (rle (app 'fixed-value 'current)
                        (radd (app 'candidate 'current) fixed-radius))]
               (left-conjunct left right
                              (app candidate-fixed-close 'current))))
            right-pointwise
            (function/lam
             [['current 'S]]
             (let [left
                   (rle (app 'candidate 'current)
                        (radd (app 'fixed-value 'current) fixed-radius))
                   right
                   (rle (app 'fixed-value 'current)
                        (radd (app 'candidate 'current) fixed-radius))]
               (right-conjunct left right
                               (app candidate-fixed-close 'current))))]
        (app
         (function/const*
          'metric/finite-nnrat-sup-radius-self-bound-of-contracted-image
          [U])
         'S 'states 'candidate image 'fixed-value 'discount
         (function/lam
          [['state 'S]
           ['ignored (source-membership U 'S 'states 'state)]]
          (app
           (function/const*
            'bellman/nnrat-policy-step-fixed-point-contraction [U V])
           'S 'A 'states 'transition 'reward 'discount
           'policy 'normalized 'fixed-value 'fixed-point
           'candidate fixed-radius left-pointwise right-pointwise 'state)))))}))

(def policy-fixed-point-residual-bound-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        image
        (function/lam
         [['state 'S]]
         (policy-step backup 'policy 'candidate 'state))
        fixed-radius (finite-radius 'S 'states 'candidate 'fixed-value)
        residual (finite-radius 'S 'states 'candidate image)]
    {:name 'bellman/nnrat-policy-fixed-point-residual-bound
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (policy-model-binders backup)
       [['candidate value-function]
        ['gap nnrat] ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]])
      (rle fixed-radius (rmul 'inverse residual)))
     :value
     (function/lam
      (concat
       (policy-model-binders backup)
       [['candidate value-function]
        ['gap nnrat] ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]])
      (app
       (function/const* 'nnrat/inverse-gap-residual-bound [])
       fixed-radius residual 'discount 'gap 'inverse
       'discount-plus-gap-one 'inverse-times-gap-one
       (apply
        app
        (function/const*
         'bellman/nnrat-policy-fixed-point-sup-radius-self-bound [U V])
        (concat policy-model-arguments ['candidate]))))}))

(def policy-fixed-point-stopping-certificate-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        image
        (function/lam
         [['state 'S]]
         (policy-step backup 'policy 'candidate 'state))
        fixed-radius (finite-radius 'S 'states 'candidate 'fixed-value)
        residual (finite-radius 'S 'states 'candidate image)]
    {:name 'bellman/nnrat-policy-fixed-point-stopping-certificate
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (policy-model-binders backup)
       [['candidate value-function]
        ['gap nnrat] ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]
        ['threshold nnrat]
        ['residual-at-most-threshold (rle residual 'threshold)]])
      (rle fixed-radius (rmul 'inverse 'threshold)))
     :value
     (function/lam
      (concat
       (policy-model-binders backup)
       [['candidate value-function]
        ['gap nnrat] ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]
        ['threshold nnrat]
        ['residual-at-most-threshold (rle residual 'threshold)]])
      (let [certified
            (apply
             app
             (function/const*
              'bellman/nnrat-policy-fixed-point-residual-bound [U V])
             (concat
              policy-model-arguments
              ['candidate 'gap 'inverse
               'discount-plus-gap-one 'inverse-times-gap-one]))
            scaled
            (app (function/const* 'nnrat/multiply-monotone [])
                 'inverse residual 'threshold
                 'residual-at-most-threshold)]
        (order-transitive
         fixed-radius (rmul 'inverse residual)
         (rmul 'inverse 'threshold) certified scaled)))}))

(def policy-fixed-point-residual-zero-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        image
        (function/lam
         [['state 'S]]
         (policy-step backup 'policy 'value 'state))]
    {:name 'bellman/nnrat-policy-fixed-point-residual-radius-zero
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['value (function/arrow 'S nnrat)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (req (policy-step backup 'policy 'value 'state)
              (app 'value 'state)))]]
      (req (finite-radius 'S 'states 'value image) nnrat-zero))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['value (function/arrow 'S nnrat)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (req (policy-step backup 'policy 'value 'state)
              (app 'value 'state)))]]
      (app
       (function/const*
        'metric/finite-nnrat-sup-radius-zero-of-pointwise-equivalent [U])
       'S 'states 'value image
       (function/lam
        [['state 'S]
         ['ignored (source-membership U 'S 'states 'state)]]
        (equivalent-symmetric
         (app image 'state) (app 'value 'state)
         (app 'fixed-point 'state)))))}))

(defn- uniqueness-binders [backup]
  [['S type-u] ['A type-v]
   ['states (exact-finset-of U 'S)]
   ['transition (function/arrow 'S 'A 'S nnrat)]
   ['reward (function/arrow 'S 'A nnrat)]
   ['discount nnrat]
   ['policy (function/arrow 'S 'A)]
   ['normalized (rows-normalized 'S 'A 'states 'transition)]
   ['state-covered
    (function/forall
     [['state 'S]]
     (source-membership U 'S 'states 'state))]
   ['left-value (function/arrow 'S nnrat)]
   ['left-fixed-point
    (function/forall
     [['state 'S]]
     (req (policy-step backup 'policy 'left-value 'state)
          (app 'left-value 'state)))]
   ['right-value (function/arrow 'S nnrat)]
   ['right-fixed-point
    (function/forall
     [['state 'S]]
     (req (policy-step backup 'policy 'right-value 'state)
          (app 'right-value 'state)))]
   ['gap nnrat] ['inverse nnrat]
   ['discount-plus-gap-one
    (req (radd 'discount 'gap) nnrat-one)]
   ['inverse-times-gap-one
    (req (rmul 'inverse 'gap) nnrat-one)]])

(def uniqueness-arguments
  ['S 'A 'states 'transition 'reward 'discount 'policy
   'normalized 'state-covered
   'left-value 'left-fixed-point 'right-value 'right-fixed-point
   'gap 'inverse 'discount-plus-gap-one 'inverse-times-gap-one])

(def policy-fixed-points-zero-radius-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        left-image
        (function/lam
         [['state 'S]]
         (policy-step backup 'policy 'left-value 'state))
        distance (finite-radius 'S 'states 'left-value 'right-value)
        residual (finite-radius 'S 'states 'left-value left-image)
        scaled-zero (rmul 'inverse nnrat-zero)]
    {:name 'bellman/nnrat-policy-fixed-points-have-zero-sup-radius
     :universes ['u 'v]
     :type
     (function/forall
      (uniqueness-binders backup)
      (req distance nnrat-zero))
     :value
     (function/lam
      (uniqueness-binders backup)
      (let [residual-zero
            (app
             (function/const*
              'bellman/nnrat-policy-fixed-point-residual-radius-zero [U V])
             'S 'A 'states 'transition 'reward 'discount
             'policy 'left-value 'left-fixed-point)
            residual-at-most-zero
            (equivalent-to-at-most residual nnrat-zero residual-zero)
            distance-at-most-scaled-zero
            (app
             (function/const*
              'bellman/nnrat-policy-fixed-point-stopping-certificate [U V])
             'S 'A 'states 'transition 'reward 'discount
             'policy 'normalized 'state-covered
             'right-value 'right-fixed-point 'left-value
             'gap 'inverse
             'discount-plus-gap-one 'inverse-times-gap-one
             nnrat-zero residual-at-most-zero)
            distance-at-most-zero
            (order-respects
             distance distance nnrat-zero scaled-zero
             (equivalent-reflexive distance)
             (equivalent-symmetric
              scaled-zero nnrat-zero
              (app (function/const* 'nnrat/multiply-zero-right [])
                   'inverse))
             distance-at-most-scaled-zero)
            zero-at-most-distance
            (app
             (function/const*
              'metric/finite-nnrat-sup-radius-nonnegative [U])
             'S 'states 'left-value 'right-value)]
        (antisymmetric distance nnrat-zero
                       distance-at-most-zero zero-at-most-distance)))}))

(def policy-fixed-points-unique-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)]
    {:name 'bellman/nnrat-policy-fixed-points-unique
     :universes ['u 'v]
     :type
     (function/forall
      (uniqueness-binders backup)
      (function/forall
       [['state 'S]]
       (req (app 'left-value 'state) (app 'right-value 'state))))
     :value
     (function/lam
      (uniqueness-binders backup)
      (let [zero-radius
            (apply
             app
             (function/const*
              'bellman/nnrat-policy-fixed-points-have-zero-sup-radius [U V])
             uniqueness-arguments)
            pointwise
            (app
             (function/const*
              'metric/pointwise-equivalent-of-finite-nnrat-sup-radius-zero
              [U])
             'S 'states 'left-value 'right-value zero-radius)]
        (function/lam
         [['state 'S]]
         (app pointwise 'state (app 'state-covered 'state)))))}))

(def definition-specs [])
(def theorem-specs
  [contracted-image-self-bound-spec
   policy-step-fixed-point-contraction-spec
   policy-fixed-point-self-bound-spec
   policy-fixed-point-residual-bound-spec
   policy-fixed-point-stopping-certificate-spec
   policy-fixed-point-residual-zero-spec
   policy-fixed-points-zero-radius-spec
   policy-fixed-points-unique-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-residual-certificate rainbow.math.rational.nnrat.metric-separation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/multiply-zero-right :nnrat-identities identities/multiply-zero-right-spec) (support/extend-with :finite-bellman-policy-residual-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-policy-residual-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
