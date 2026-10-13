(ns rainbow.math.finite.bellman-residual-certificate
  "A posteriori certificates for exact finite NNRAT Bellman solvers.

  For an exhaustive finite state carrier, the exact supremum radius and the
  Bellman contraction theorem give

      radius(candidate, fixed)
        <= radius(candidate, T candidate)
           + discount * radius(candidate, fixed).

  The NNRAT inverse-gap theorem then turns the computable Bellman residual into
  a sharp error certificate.  A final stopping theorem accepts a checked
  residual threshold directly.  Exhaustiveness is an explicit premise:
  `state-covered` proves that every inhabitant of S occurs in `states`; no
  finite fold is silently treated as covering a larger carrier.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-value-iteration-converges
             :as bellman-convergence]
            [rainbow.math.finite.nnrat-sup-radius :as radius]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]
            [rainbow.math.rational.nnrat.farkas-elim-list :as nnrat-bounds]
            [rainbow.math.rational.nnrat.inverse-gap-certificate :as inverse-gap]
            [rainbow.math.rational.nnrat.product-reassociation :as product-reassociation]
            [rainbow.math.rational.nnrat.ring :as ring]
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
(defn- optimality-step
  [state action actions fallback backup value current]
  (app (function/const* 'value/nnrat-optimality-step [U V])
       state action actions fallback backup value current))
(defn- order-reflexive [value]
  (app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- order-respects
  [left equivalent-left right equivalent-right
   same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left equivalent-left right equivalent-right
       same-left same-right ordered))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- close [left right epsilon]
  (proposition/conjunction
   (rle left (radd right epsilon))
   (rle right (radd left epsilon))))
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
(defn- zero-at-most [value]
  (app (function/const* 'nnrat/zero-at-most []) value))

(defn- model-binders [backup]
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
   ['fixed-value (function/arrow 'S nnrat)]
   ['fixed-point
    (function/forall
     [['state 'S]]
     (req
      (optimality-step 'S 'A 'actions 'fallback backup
                       'fixed-value 'state)
      (app 'fixed-value 'state)))]])

(def model-arguments
  ['S 'A 'states 'actions 'transition 'reward 'discount
   'fallback 'fallback-admissible 'normalized 'state-covered
   'fixed-value 'fixed-point])

(def additive-upper-triangle-spec
  {:name 'nnrat/additive-upper-triangle
   :universes []
   :type
   (function/forall
    [['left nnrat] ['middle nnrat] ['right nnrat]
     ['first-radius nnrat] ['second-radius nnrat]
     ['first-bound
      (rle 'left (radd 'middle 'first-radius))]
     ['second-bound
      (rle 'middle (radd 'right 'second-radius))]]
    (rle 'left
         (radd 'right (radd 'first-radius 'second-radius))))
   :value
   (function/lam
    [['left nnrat] ['middle nnrat] ['right nnrat]
     ['first-radius nnrat] ['second-radius nnrat]
     ['first-bound
      (rle 'left (radd 'middle 'first-radius))]
     ['second-bound
      (rle 'middle (radd 'right 'second-radius))]]
    (let [old-upper
          (radd (radd 'right 'second-radius) 'first-radius)
          new-upper
          (radd 'right (radd 'first-radius 'second-radius))
          lifted
          (app (function/const* 'nnrat/add-right-monotone [])
               'first-radius 'middle (radd 'right 'second-radius)
               'second-bound)
          chained
          (order-transitive
           'left (radd 'middle 'first-radius) old-upper
           'first-bound lifted)]
      (order-respects
       'left 'left new-upper old-upper
       (equivalent-reflexive 'left)
       (ring/equiv new-upper old-upper)
       chained)))})

(def optimality-fixed-point-sup-radius-self-bound-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        step-value
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup
                          'candidate 'state))
        fixed-radius
        (finite-radius 'S 'states 'candidate 'fixed-value)
        residual-radius
        (finite-radius 'S 'states 'candidate step-value)
        contracted-radius (rmul 'discount fixed-radius)
        self-upper (radd residual-radius contracted-radius)]
    {:name 'value/nnrat-optimality-fixed-point-sup-radius-self-bound
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (model-binders backup)
       [['candidate value-function]])
      (rle fixed-radius self-upper))
     :value
     (function/lam
      (concat
       (model-binders backup)
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
               (left-conjunct
                left right (app candidate-fixed-close 'current))))
            right-pointwise
            (function/lam
             [['current 'S]]
             (let [left
                   (rle (app 'candidate 'current)
                        (radd (app 'fixed-value 'current) fixed-radius))
                   right
                   (rle (app 'fixed-value 'current)
                        (radd (app 'candidate 'current) fixed-radius))]
               (right-conjunct
                left right (app candidate-fixed-close 'current))))
            pointwise
            (function/lam
             [['current 'S]
              ['member
               (source-membership U 'S 'states 'current)]]
             (let [candidate-at (app 'candidate 'current)
                   step-at (app step-value 'current)
                   fixed-at (app 'fixed-value 'current)
                   residual-close
                   (additive-closeness
                    candidate-at step-at residual-radius
                    (radius-upper-bound
                     'S 'states 'candidate step-value 'current 'member))
                   candidate-step
                   (left-conjunct
                    (rle candidate-at (radd step-at residual-radius))
                    (rle step-at (radd candidate-at residual-radius))
                    residual-close)
                   step-candidate
                   (right-conjunct
                    (rle candidate-at (radd step-at residual-radius))
                    (rle step-at (radd candidate-at residual-radius))
                    residual-close)
                   contracted-close
                   (app
                    (function/const*
                     'value/nnrat-optimality-step-fixed-point-contraction
                     [U V])
                    'S 'A 'states 'actions 'transition 'reward 'discount
                    'fallback 'fallback-admissible 'normalized
                    'fixed-value 'fixed-point
                    'candidate fixed-radius
                    left-pointwise right-pointwise 'current)
                   step-fixed
                   (left-conjunct
                    (rle step-at (radd fixed-at contracted-radius))
                    (rle fixed-at (radd step-at contracted-radius))
                    contracted-close)
                   fixed-step
                   (right-conjunct
                    (rle step-at (radd fixed-at contracted-radius))
                    (rle fixed-at (radd step-at contracted-radius))
                    contracted-close)
                   candidate-fixed
                   (app
                    (function/const* 'nnrat/additive-upper-triangle [])
                    candidate-at step-at fixed-at
                    residual-radius contracted-radius
                    candidate-step step-fixed)
                   reverse-upper
                   (radd candidate-at
                         (radd contracted-radius residual-radius))
                   fixed-candidate-reversed
                   (app
                    (function/const* 'nnrat/additive-upper-triangle [])
                    fixed-at step-at candidate-at
                    contracted-radius residual-radius
                    fixed-step step-candidate)
                   fixed-candidate
                   (order-respects
                    fixed-at fixed-at
                    (radd candidate-at self-upper) reverse-upper
                    (equivalent-reflexive fixed-at)
                    (ring/equiv
                     (radd candidate-at self-upper) reverse-upper)
                    fixed-candidate-reversed)]
               (distance-of-closeness
                candidate-at fixed-at self-upper
                candidate-fixed fixed-candidate)))]
        (app
         (function/const* 'metric/finite-nnrat-sup-radius-bounded [U])
         'S 'states 'candidate 'fixed-value self-upper
         (zero-at-most self-upper)
         pointwise)))}))

(def optimality-fixed-point-residual-bound-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        step-value
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup
                          'candidate 'state))
        fixed-radius
        (finite-radius 'S 'states 'candidate 'fixed-value)
        residual-radius
        (finite-radius 'S 'states 'candidate step-value)]
    {:name 'value/nnrat-optimality-fixed-point-residual-bound
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (model-binders backup)
       [['candidate value-function]
        ['gap nnrat]
        ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]])
      (rle fixed-radius (rmul 'inverse residual-radius)))
     :value
     (function/lam
      (concat
       (model-binders backup)
       [['candidate value-function]
        ['gap nnrat]
        ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]])
      (app
       (function/const* 'nnrat/inverse-gap-residual-bound [])
       fixed-radius residual-radius 'discount 'gap 'inverse
       'discount-plus-gap-one 'inverse-times-gap-one
       (apply
        app
        (function/const*
         'value/nnrat-optimality-fixed-point-sup-radius-self-bound [U V])
        (concat model-arguments ['candidate]))))}))

(def optimality-fixed-point-stopping-certificate-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        step-value
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup
                          'candidate 'state))
        fixed-radius
        (finite-radius 'S 'states 'candidate 'fixed-value)
        residual-radius
        (finite-radius 'S 'states 'candidate step-value)]
    {:name 'value/nnrat-optimality-fixed-point-stopping-certificate
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (model-binders backup)
       [['candidate value-function]
        ['gap nnrat]
        ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]
        ['threshold nnrat]
        ['residual-at-most-threshold
         (rle residual-radius 'threshold)]])
      (rle fixed-radius (rmul 'inverse 'threshold)))
     :value
     (function/lam
      (concat
       (model-binders backup)
       [['candidate value-function]
        ['gap nnrat]
        ['inverse nnrat]
        ['discount-plus-gap-one
         (req (radd 'discount 'gap) nnrat-one)]
        ['inverse-times-gap-one
         (req (rmul 'inverse 'gap) nnrat-one)]
        ['threshold nnrat]
        ['residual-at-most-threshold
         (rle residual-radius 'threshold)]])
      (let [certified
            (apply
             app
             (function/const*
              'value/nnrat-optimality-fixed-point-residual-bound [U V])
             (concat
              model-arguments
              ['candidate 'gap 'inverse
               'discount-plus-gap-one 'inverse-times-gap-one]))
            scaled-threshold
            (app (function/const* 'nnrat/multiply-monotone [])
                 'inverse residual-radius 'threshold
                 'residual-at-most-threshold)]
        (order-transitive
         fixed-radius (rmul 'inverse residual-radius)
         (rmul 'inverse 'threshold)
         certified scaled-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [additive-upper-triangle-spec
   optimality-fixed-point-sup-radius-self-bound-spec
   optimality-fixed-point-residual-bound-spec
   optimality-fixed-point-stopping-certificate-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-value-iteration-converges rainbow.math.finite.nnrat-sup-radius])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :nnrat-add-cancellation cancellation/theorem-specs) (extend-specs-if-missing :nnrat-product-reassociation product-reassociation/theorem-specs) (extend-spec-if-missing 'nnrat/zero-at-most :nnrat-farkas-elim-list nnrat-bounds/zero-at-most-spec) (extend-spec-if-missing 'nnrat/inverse-gap-residual-bound :nnrat-inverse-gap-certificate inverse-gap/inverse-gap-residual-bound-spec) (support/extend-with :finite-bellman-residual-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-residual-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
