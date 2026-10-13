(ns rainbow.math.finite.bellman-signed-fixed-point-uniqueness
  "Uniqueness of signed Bellman optimality fixed points.

  Treat the first fixed point as a residual-certified candidate relative to the
  second.  Its Bellman residual has zero finite signed sup distance, so the
  exact inverse-gap certificate forces the distance between the fixed points to
  zero.  Finite signed metric separation then yields pointwise quotient
  equivalence over the entire carrier, using the explicit coverage witness.

  This proves uniqueness, not existence.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-greedy-policy :as greedy]
            [rainbow.math.finite.signed-sup-separation :as separation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
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
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))

(def signed-optimality-fixed-points-unique-spec
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
          (optimality-step
           'S 'A 'actions 'fallback backup 'value 'state)))
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
           (req
            (nnrat-total-mass
             'S 'states (app 'transition 'state 'action))
            nnrat-one))]
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
    {:name 'value/nnrat-transition-signed-optimality-fixed-points-unique
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
      (let [residual-zero
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
            residual-bound
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-fixed-point-residual-bound
              [U V])
             'S 'A 'states 'state-covered 'actions
             'transition 'reward 'discount
             'fallback 'fallback-admissible 'normalized
             'right 'right-fixed 'left
             'gap 'inverse 'inverse-nonnegative
             'discount-plus-gap-one 'inverse-times-gap-one)
            scaled-zero
            (equivalent-transitive
             scaled-residual (smul 'inverse signed-zero) signed-zero
             (app
              (function/const*
               'signed/multiply-left-respects-equivalence [])
              residual signed-zero 'inverse residual-zero)
             (app (function/const* 'signed/multiply-zero-right [])
                  'inverse))
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

(def definition-specs [])
(def theorem-specs [signed-optimality-fixed-points-unique-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(defn extend-environment [env]
  (-> env
      greedy/extend-environment
      (extend-specs-if-missing
       :finite-signed-sup-separation separation/theorem-specs)
      (support/extend-with
       :finite-bellman-signed-fixed-point-uniqueness theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
