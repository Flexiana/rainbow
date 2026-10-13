(ns rainbow.math.finite.bellman-signed-residual-certificate
  "A posteriori residual certificates for signed Bellman optimality.

  A generic finite-function theorem combines the signed sup metric, scalar
  triangle inequality, and a two-sided additive contraction to establish

      d(v,v*) <= d(v,Tv) + rate*d(v,v*).

  The checked signed inverse-gap theorem then isolates the unknown fixed-point
  distance.  Bellman capstones instantiate the generic result with ordinary
  normalized nnrat transition kernels, arbitrary signed rewards and values,
  and the runtime finite-action maximum.

  This verifies mathematical certificates, not an executable solver.  State
  coverage and fixed-point existence remain explicit premises.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
             :as bellman]
            [rainbow.math.linear.matrix.affine-inverse-gap-certificate
             :as inverse-gap]
            [rainbow.math.finite.signed-sup-distance :as metric]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
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
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- finite-distance [level element source left right]
  (app (function/const* 'metric/finite-signed-sup-distance [level])
       element source left right))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def finite-signed-sup-distance-self-bound-spec
  (let [value-function (function/arrow 'S signed)
        image (fn [value] (app 'operator value))
        distance (finite-distance U 'S 'states 'candidate 'fixed-value)
        residual (finite-distance U 'S 'states 'candidate (image 'candidate))
        contracted (smul 'rate distance)
        self-upper (sadd residual contracted)
        close
        (fn [left right epsilon]
          (proposition/conjunction
           (sle left (sadd right epsilon))
           (sle right (sadd left epsilon))))]
    {:name 'metric/finite-signed-sup-distance-self-bound-of-additive-contraction
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['states (exact-finset-of U 'S)]
       ['state-covered
        (function/forall
         [['state 'S]]
         (source-membership U 'S 'states 'state))]
       ['operator (function/arrow value-function value-function)]
       ['rate signed]
       ['rate-nonnegative (sle signed-zero 'rate)]
       ['contractive
        (function/forall
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
         (close (app (image 'left-value) 'state)
                (app (image 'right-value) 'state)
                (smul 'rate 'epsilon)))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (app (image 'fixed-value) 'state)
              (app 'fixed-value 'state)))]
       ['candidate value-function]]
      (sle distance self-upper))
     :value
     (function/lam
      [['S type-u]
       ['states (exact-finset-of U 'S)]
       ['state-covered
        (function/forall
         [['state 'S]]
         (source-membership U 'S 'states 'state))]
       ['operator (function/arrow value-function value-function)]
       ['rate signed]
       ['rate-nonnegative (sle signed-zero 'rate)]
       ['contractive
        (function/forall
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
         (close (app (image 'left-value) 'state)
                (app (image 'right-value) 'state)
                (smul 'rate 'epsilon)))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (veq (app (image 'fixed-value) 'state)
              (app 'fixed-value 'state)))]
       ['candidate value-function]]
      (let [candidate-fixed-close
            (function/lam
             [['state 'S]]
             (app
              (function/const*
               'signed/additive-closeness-of-distance-at-most [])
              (app 'candidate 'state)
              (app 'fixed-value 'state)
              distance
              (app
               (function/const*
                'metric/finite-signed-sup-distance-upper-bound [U])
               'S 'states 'candidate 'fixed-value
               'state (app 'state-covered 'state))))
            left-pointwise
            (function/lam
             [['state 'S]]
             (let [left
                   (sle (app 'candidate 'state)
                        (sadd (app 'fixed-value 'state) distance))
                   right
                   (sle (app 'fixed-value 'state)
                        (sadd (app 'candidate 'state) distance))]
               (left-conjunct
                left right (app candidate-fixed-close 'state))))
            right-pointwise
            (function/lam
             [['state 'S]]
             (let [left
                   (sle (app 'candidate 'state)
                        (sadd (app 'fixed-value 'state) distance))
                   right
                   (sle (app 'fixed-value 'state)
                        (sadd (app 'candidate 'state) distance))]
               (right-conjunct
                left right (app candidate-fixed-close 'state))))
            pointwise
            (function/lam
             [['state 'S]
              ['member (source-membership U 'S 'states 'state)]]
             (let [candidate-at (app 'candidate 'state)
                   candidate-image-at (app (image 'candidate) 'state)
                   fixed-image-at (app (image 'fixed-value) 'state)
                   fixed-at (app 'fixed-value 'state)
                   contracted-close
                   (app 'contractive
                        'candidate 'fixed-value distance
                        left-pointwise right-pointwise 'state)
                   image-pair-distance
                   (scalar-distance candidate-image-at fixed-image-at)
                   image-fixed-distance
                   (scalar-distance candidate-image-at fixed-at)
                   image-pair-bound
                   (app
                    (function/const*
                     'signed/distance-at-most-of-additive-closeness [])
                    candidate-image-at fixed-image-at contracted
                    (left-conjunct
                     (sle candidate-image-at
                          (sadd fixed-image-at contracted))
                     (sle fixed-image-at
                          (sadd candidate-image-at contracted))
                     contracted-close)
                    (right-conjunct
                     (sle candidate-image-at
                          (sadd fixed-image-at contracted))
                     (sle fixed-image-at
                          (sadd candidate-image-at contracted))
                     contracted-close))
                   image-fixed-same
                   (app
                    (function/const*
                     'signed/distance-respects-equivalence [])
                    candidate-image-at candidate-image-at
                    fixed-image-at fixed-at
                    (equivalent-reflexive candidate-image-at)
                    (app 'fixed-point 'state))
                   image-fixed-bound
                   (order-respects
                    image-pair-distance image-fixed-distance
                    contracted contracted
                    image-fixed-same (equivalent-reflexive contracted)
                    image-pair-bound)
                   residual-at-state
                   (scalar-distance candidate-at candidate-image-at)
                   residual-bound
                   (app
                    (function/const*
                     'metric/finite-signed-sup-distance-upper-bound [U])
                    'S 'states 'candidate (image 'candidate)
                    'state 'member)
                   triangle
                   (app (function/const* 'signed/distance-triangle [])
                        candidate-at candidate-image-at fixed-at)
                   components
                   (app (function/const* 'signed/add-monotone [])
                        residual-at-state residual
                        image-fixed-distance contracted
                        residual-bound image-fixed-bound)]
               (order-transitive
                (scalar-distance candidate-at fixed-at)
                (sadd residual-at-state image-fixed-distance)
                self-upper triangle components)))
            residual-nonnegative
            (app
             (function/const*
              'metric/finite-signed-sup-distance-nonnegative [U])
             'S 'states 'candidate (image 'candidate))
            distance-nonnegative
            (app
             (function/const*
              'metric/finite-signed-sup-distance-nonnegative [U])
             'S 'states 'candidate 'fixed-value)
            contracted-nonnegative
            (app
             (function/const* 'signed/zero-at-most-of-nonnegative [])
             contracted
             (app
              (function/const* 'signed/multiply-nonnegative [])
              'rate distance
              (app
               (function/const* 'signed/nonnegative-of-zero-at-most [])
               'rate 'rate-nonnegative)
              (app
               (function/const* 'signed/nonnegative-of-zero-at-most [])
               distance distance-nonnegative)))
            zero-sum (sadd signed-zero signed-zero)
            zero-upper
            (order-respects
             zero-sum signed-zero self-upper self-upper
             (app (function/const* 'signed/add-zero-right []) signed-zero)
             (equivalent-reflexive self-upper)
             (app (function/const* 'signed/add-monotone [])
                  signed-zero residual
                  signed-zero contracted
                  residual-nonnegative contracted-nonnegative))]
        (app
         (function/const*
          'metric/finite-signed-sup-distance-bounded [U])
         'S 'states 'candidate 'fixed-value self-upper
         zero-upper pointwise)))}))

(defn- bellman-model-binders [backup]
  (let [value-function (function/arrow 'S signed)]
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
     ['fixed-value value-function]
     ['fixed-point
      (function/forall
       [['state 'S]]
       (veq
        (optimality-step
         'S 'A 'actions 'fallback backup 'fixed-value 'state)
        (app 'fixed-value 'state)))]
     ['candidate value-function]]))

(defn- bellman-objects []
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
           'S 'A 'actions 'fallback backup 'value 'state)))]
    {:value-function value-function
     :backup backup
     :operator operator
     :rate rate}))

(def signed-optimality-self-bound-spec
  (let [{:keys [backup operator rate]} (bellman-objects)
        distance (finite-distance U 'S 'states 'candidate 'fixed-value)
        residual (finite-distance U 'S 'states 'candidate (app operator 'candidate))]
    {:name 'value/nnrat-transition-signed-optimality-fixed-point-sup-distance-self-bound
     :universes ['u 'v]
     :type
     (function/forall
      (bellman-model-binders backup)
      (sle distance (sadd residual (smul rate distance))))
     :value
     (function/lam
      (bellman-model-binders backup)
      (app
       (function/const*
        'metric/finite-signed-sup-distance-self-bound-of-additive-contraction [U])
       'S 'states 'state-covered operator rate
       (app (function/const* 'signed/zero-at-most-from-nnrat []) 'discount)
       (function/lam
        [['left-value (function/arrow 'S signed)]
         ['right-value (function/arrow 'S signed)]
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
          'value/nnrat-transition-signed-optimality-step-additively-contractive
          [U V])
         'S 'A 'states 'actions 'transition 'reward 'discount
         'fallback 'fallback-admissible 'normalized
         'left-value 'right-value 'epsilon
         'left-pointwise 'right-pointwise 'state))
       'fixed-value 'fixed-point 'candidate))}))

(def signed-optimality-residual-bound-spec
  (let [{:keys [backup operator rate]} (bellman-objects)
        distance (finite-distance U 'S 'states 'candidate 'fixed-value)
        residual (finite-distance U 'S 'states 'candidate (app operator 'candidate))
        binders
        (concat
         (bellman-model-binders backup)
         [['gap signed] ['inverse signed]
          ['inverse-nonnegative (sle signed-zero 'inverse)]
          ['discount-plus-gap-one
           (veq (sadd rate 'gap) (function/const* 'signed/one []))]
          ['inverse-times-gap-one
           (veq (smul 'inverse 'gap)
                (function/const* 'signed/one []))]])]
    {:name 'value/nnrat-transition-signed-optimality-fixed-point-residual-bound
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
       (apply
        app
        (function/const*
         'value/nnrat-transition-signed-optimality-fixed-point-sup-distance-self-bound
         [U V])
        (concat
         ['S 'A 'states 'state-covered 'actions 'transition 'reward 'discount
          'fallback 'fallback-admissible 'normalized
          'fixed-value 'fixed-point 'candidate]))))}))

(def signed-optimality-stopping-certificate-spec
  (let [{:keys [backup operator rate]} (bellman-objects)
        distance (finite-distance U 'S 'states 'candidate 'fixed-value)
        residual (finite-distance U 'S 'states 'candidate (app operator 'candidate))
        base-binders
        (concat
         (bellman-model-binders backup)
         [['gap signed] ['inverse signed]
          ['inverse-nonnegative (sle signed-zero 'inverse)]
          ['discount-plus-gap-one
           (veq (sadd rate 'gap) (function/const* 'signed/one []))]
          ['inverse-times-gap-one
           (veq (smul 'inverse 'gap)
                (function/const* 'signed/one []))]])
        binders
        (concat
         base-binders
         [['threshold signed]
          ['residual-at-most-threshold (sle residual 'threshold)]])]
    {:name 'value/nnrat-transition-signed-optimality-fixed-point-stopping-certificate
     :universes ['u 'v]
     :type
     (function/forall binders
                      (sle distance (smul 'inverse 'threshold)))
     :value
     (function/lam
      binders
      (let [certified
            (apply
             app
             (function/const*
              'value/nnrat-transition-signed-optimality-fixed-point-residual-bound
              [U V])
             (concat
              ['S 'A 'states 'state-covered 'actions 'transition 'reward 'discount
               'fallback 'fallback-admissible 'normalized
               'fixed-value 'fixed-point 'candidate
               'gap 'inverse 'inverse-nonnegative
               'discount-plus-gap-one 'inverse-times-gap-one]))
            scaled-threshold
            (app (function/const* 'signed/multiply-left-monotone [])
                 'inverse residual 'threshold
                 'inverse-nonnegative 'residual-at-most-threshold)]
        (order-transitive
         distance (smul 'inverse residual)
         (smul 'inverse 'threshold)
         certified scaled-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [finite-signed-sup-distance-self-bound-spec
   signed-optimality-self-bound-spec
   signed-optimality-residual-bound-spec
   signed-optimality-stopping-certificate-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.signed-sup-distance rainbow.math.finite.bellman-signed-value-iteration-general-converges])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :signed-additive-distance additive-distance/theorem-specs) (extend-specs-if-missing :finite-matrix-affine-inverse-gap-certificate [inverse-gap/inverse-gap-residual-bound-spec]) (support/extend-with :finite-bellman-signed-residual-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-residual-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
