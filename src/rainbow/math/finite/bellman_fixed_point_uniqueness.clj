(ns rainbow.math.finite.bellman-fixed-point-uniqueness
  "Constructive uniqueness of exact finite NNRAT Bellman optimality fixed points.

  A fixed point has zero computable Bellman residual radius.  The sharp
  inverse-gap stopping certificate therefore forces the finite supremum radius
  between any two fixed points to zero, and NNRAT metric separation turns that
  into pointwise quotient equivalence.

  As in the residual certificate, `state-covered` explicitly proves that the
  exact finite state enumeration exhausts S.  This is what upgrades finite-fold
  bounds to the carrier-wide premise required by Bellman contraction.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-residual-certificate
             :as certificate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.metric-separation :as separation]))

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
(defn- optimality-step
  [state action actions fallback backup value current]
  (app (function/const* 'value/nnrat-optimality-step [U V])
       state action actions fallback backup value current))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'nnrat/equivalent-to-at-most [])
       left right same))
(defn- order-respects
  [left equivalent-left right equivalent-right
   same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left equivalent-left right equivalent-right
       same-left same-right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'nnrat/at-most-antisymmetric [])
       left right left-right right-left))

(defn- residual-binders [backup]
  [['S type-u]
   ['A type-v]
   ['states (exact-finset-of U 'S)]
   ['actions (exact-finset-of V 'A)]
   ['transition (function/arrow 'S 'A 'S nnrat)]
   ['reward (function/arrow 'S 'A nnrat)]
   ['discount nnrat]
   ['fallback (function/arrow 'S 'A)]
   ['candidate (function/arrow 'S nnrat)]
   ['candidate-fixed-point
    (function/forall
     [['state 'S]]
     (req
      (optimality-step 'S 'A 'actions 'fallback backup
                       'candidate 'state)
      (app 'candidate 'state)))]])

(defn- uniqueness-binders [backup]
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
   ['left-value (function/arrow 'S nnrat)]
   ['left-fixed-point
    (function/forall
     [['state 'S]]
     (req
      (optimality-step 'S 'A 'actions 'fallback backup
                       'left-value 'state)
      (app 'left-value 'state)))]
   ['right-value (function/arrow 'S nnrat)]
   ['right-fixed-point
    (function/forall
     [['state 'S]]
     (req
      (optimality-step 'S 'A 'actions 'fallback backup
                       'right-value 'state)
      (app 'right-value 'state)))]
   ['gap nnrat]
   ['inverse nnrat]
   ['discount-plus-gap-one
    (req (radd 'discount 'gap) nnrat-one)]
   ['inverse-times-gap-one
    (req (rmul 'inverse 'gap) nnrat-one)]])

(def uniqueness-arguments
  ['S 'A 'states 'actions 'transition 'reward 'discount
   'fallback 'fallback-admissible 'normalized 'state-covered
   'left-value 'left-fixed-point 'right-value 'right-fixed-point
   'gap 'inverse 'discount-plus-gap-one 'inverse-times-gap-one])

(def optimality-fixed-point-residual-radius-zero-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        step-value
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup
                          'candidate 'state))]
    {:name 'value/nnrat-optimality-fixed-point-residual-radius-zero
     :universes ['u 'v]
     :type
     (function/forall
      (residual-binders backup)
      (req
       (finite-radius 'S 'states 'candidate step-value)
       nnrat-zero))
     :value
     (function/lam
      (residual-binders backup)
      (app
       (function/const*
        'metric/finite-nnrat-sup-radius-zero-of-pointwise-equivalent
        [U])
       'S 'states 'candidate step-value
       (function/lam
        [['state 'S]
         ['ignored (source-membership U 'S 'states 'state)]]
        (equivalent-symmetric
         (app step-value 'state) (app 'candidate 'state)
         (app 'candidate-fixed-point 'state)))))}))

(def optimality-fixed-points-zero-radius-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        left-step
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup
                          'left-value 'state))
        distance
        (finite-radius 'S 'states 'left-value 'right-value)
        residual
        (finite-radius 'S 'states 'left-value left-step)
        scaled-zero (rmul 'inverse nnrat-zero)]
    {:name 'value/nnrat-optimality-fixed-points-have-zero-sup-radius
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
              'value/nnrat-optimality-fixed-point-residual-radius-zero
              [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'left-value 'left-fixed-point)
            residual-at-most-zero
            (equivalent-to-at-most residual nnrat-zero residual-zero)
            distance-at-most-scaled-zero
            (app
             (function/const*
              'value/nnrat-optimality-fixed-point-stopping-certificate
              [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'fallback-admissible 'normalized 'state-covered
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
        (antisymmetric
         distance nnrat-zero
         distance-at-most-zero zero-at-most-distance)))}))

(def optimality-fixed-points-unique-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        distance
        (finite-radius 'S 'states 'left-value 'right-value)]
    {:name 'value/nnrat-optimality-fixed-points-unique
     :universes ['u 'v]
     :type
     (function/forall
      (uniqueness-binders backup)
      (function/forall
       [['state 'S]]
       (req (app 'left-value 'state)
            (app 'right-value 'state))))
     :value
     (function/lam
      (uniqueness-binders backup)
      (let [zero-radius
            (apply
             app
             (function/const*
              'value/nnrat-optimality-fixed-points-have-zero-sup-radius
              [U V])
             uniqueness-arguments)
            equivalent-on-support
            (app
             (function/const*
              'metric/pointwise-equivalent-of-finite-nnrat-sup-radius-zero
              [U])
             'S 'states 'left-value 'right-value zero-radius)]
        (function/lam
         [['state 'S]]
         (app equivalent-on-support
              'state (app 'state-covered 'state)))))}))

(def definition-specs [])
(def theorem-specs
  [optimality-fixed-point-residual-radius-zero-spec
   optimality-fixed-points-zero-radius-spec
   optimality-fixed-points-unique-spec])

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
  (-> env (extend-spec-if-missing 'nnrat/multiply-zero-right :nnrat-identities identities/multiply-zero-right-spec) (support/extend-with :finite-bellman-fixed-point-uniqueness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-fixed-point-uniqueness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
