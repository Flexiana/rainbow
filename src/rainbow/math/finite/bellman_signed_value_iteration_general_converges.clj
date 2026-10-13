(ns rainbow.math.finite.bellman-signed-value-iteration-general-converges
  "General strict-rate convergence for signed Bellman value iteration.

  Any nnrat rate-null sequence remains rate-null after the Grothendieck
  embedding.  For the canonical strict rational rate

      gamma = (ap+1)/(ap+gp+2),

  the exact signed power recurrence is dominated by the embedded general
  harmonic sequence.  It therefore inherits the established modulus
  `(ap+1)*k`.  Transporting that certificate to the signed Bellman error-radius
  removes the earlier discount-at-most-one-half restriction.

  The Bellman capstone still assumes a normalized nnrat transition kernel and
  existence of a signed fixed point.  Native, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-value-iteration-converges
             :as half-convergence]
            [rainbow.math.linear.matrix.affine-nnrat-exact-rate :as exact-rate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.general-contraction :as general-contraction]
            [rainbow.math.rational.nnrat.general-harmonic :as general-harmonic]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.geometric-bridge :as signed-bridge]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- seq-equiv [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- nnrat-rate-null [sequence modulus]
  (app (function/const* 'analysis/rate-null []) sequence modulus))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
(defn- general-harmonic-at [ap gp steps]
  (app (function/const* 'nnrat/general-harmonic []) ap gp steps))
(defn- harmonic-at [steps]
  (app (function/const* 'nnrat/harmonic []) steps))
(defn- power-scale [gamma steps value]
  (app (function/const* 'signed/nnrat-power-scale [])
       gamma steps value))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- iterate-value [state action actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       state action actions fallback backup steps initial))
(defn- equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equiv-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects
  [left left-prime right right-prime left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))

(def signed-rate-null-from-nnrat-spec
  (let [nnrat-sequence-type (function/arrow nat nnrat)
        signed-sequence
        (function/lam
         [['steps nat]] (from-nnrat (app 'sequence 'steps)))]
    {:name 'analysis/signed-rate-null-from-nnrat
     :universes []
     :type
     (function/forall
      [['sequence nnrat-sequence-type]
       ['modulus (function/arrow nat nat)]
       ['null (nnrat-rate-null 'sequence 'modulus)]]
      (signed-rate-null signed-sequence 'modulus))
     :value
     (function/lam
      [['sequence nnrat-sequence-type]
       ['modulus (function/arrow nat nat)]
       ['null (nnrat-rate-null 'sequence 'modulus)]
       ['index nat] ['steps nat]
       ['large-enough
        (app (function/const* 'nat/at-most [])
             (app 'modulus 'index) 'steps)]]
      (let [value (app 'sequence 'steps)
            radius (harmonic-at 'index)
            embedded-value (from-nnrat value)
            embedded-radius (from-nnrat radius)]
        (conjoin
         (sle signed-zero embedded-value)
         (sle embedded-value embedded-radius)
         (app (function/const* 'signed/zero-at-most-from-nnrat []) value)
         (app (function/const* 'signed/from-nnrat-at-most [])
              value radius (app 'null 'index 'steps 'large-enough)))))}))

(def signed-general-harmonic-rate-null-spec
  (let [sequence
        (function/lam
         [['steps nat]]
         (from-nnrat (general-harmonic-at 'ap 'gp 'steps)))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'analysis/signed-general-harmonic-rate-null
     :universes []
     :type
     (function/forall
      [['ap nat] ['gp nat]]
      (signed-rate-null sequence modulus))
     :value
     (function/lam
      [['ap nat] ['gp nat]]
      (app
       (function/const* 'analysis/signed-rate-null-from-nnrat [])
       (app (function/const* 'nnrat/general-harmonic []) 'ap 'gp)
       modulus
       (app (function/const* 'analysis/general-harmonic-null [])
            'ap 'gp)))}))

(def power-scale-general-harmonic-bound-spec
  (let [gamma
        (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        power (fn [steps] (power-scale gamma steps 'initial-error))
        bound (fn [steps] (general-harmonic-at 'ap 'gp steps))
        embedded-bound (fn [steps] (from-nnrat (bound steps)))
        motive
        (function/lam
         [['steps nat]]
         (sle (power 'steps) (embedded-bound 'steps)))]
    {:name 'signed/nnrat-power-scale-general-harmonic-bound
     :universes []
     :type
     (function/forall
      [['ap nat] ['gp nat] ['initial-error signed]
       ['initial-bound
        (sle 'initial-error (embedded-bound nat-zero))]
       ['steps nat]]
      (sle (power 'steps) (embedded-bound 'steps)))
     :value
     (function/lam
      [['ap nat] ['gp nat] ['initial-error signed]
       ['initial-bound
        (sle 'initial-error (embedded-bound nat-zero))]
       ['steps nat]]
      (let [rate (from-nnrat gamma)
            rate-nonnegative
            (app (function/const* 'signed/zero-at-most-from-nnrat []) gamma)
            step
            (function/lam
             [['previous-steps nat]
              ['induction-hypothesis (app motive 'previous-steps)]]
             (let [previous-power (power 'previous-steps)
                   current-bound (bound 'previous-steps)
                   next-bound (bound (succ 'previous-steps))
                   embedded-current (from-nnrat current-bound)
                   raw-product (smul rate embedded-current)
                   nnrat-product (rmul gamma current-bound)
                   embedded-product (from-nnrat nnrat-product)
                   embedded-next (from-nnrat next-bound)
                   monotone-product
                   (app
                    (function/const* 'signed/multiply-left-monotone [])
                    rate previous-power embedded-current
                    rate-nonnegative 'induction-hypothesis)
                   product-same
                   (app (function/const* 'signed/from-nnrat-multiply [])
                        gamma current-bound)
                   to-embedded-product
                   (order-respects
                    (smul rate previous-power)
                    (smul rate previous-power)
                    raw-product embedded-product
                    (equiv-reflexive (smul rate previous-power))
                    product-same monotone-product)
                   harmonic-step
                   (app (function/const* 'nnrat/general-harmonic-step [])
                        'ap 'gp 'previous-steps)
                   embedded-step
                   (app (function/const* 'signed/from-nnrat-at-most [])
                        nnrat-product next-bound harmonic-step)]
               (order-transitive
                (power (succ 'previous-steps))
                embedded-product embedded-next
                to-embedded-product embedded-step)))]
        (app (function/const* 'data/Nat.rec [zero-level])
             motive 'initial-bound step 'steps)))}))

(def signed-power-rate-null-general-spec
  (let [gamma
        (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        source
        (function/lam
         [['steps nat]]
         (from-nnrat (general-harmonic-at 'ap 'gp 'steps)))
        target
        (function/lam
         [['steps nat]] (power-scale gamma 'steps 'initial-error))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'analysis/signed-nnrat-power-rate-null-general
     :universes []
     :type
     (function/forall
      [['ap nat] ['gp nat]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]]
      (signed-rate-null target modulus))
     :value
     (function/lam
      [['ap nat] ['gp nat]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]]
      (app
       (function/const* 'analysis/signed-rate-null-dominated [])
       source target modulus
       (function/lam
        [['steps nat]]
        (app (function/const* 'signed/nnrat-power-scale-nonnegative [])
             gamma 'initial-error 'initial-error-nonnegative 'steps))
       (function/lam
        [['steps nat]]
        (app
         (function/const* 'signed/nnrat-power-scale-general-harmonic-bound [])
         'ap 'gp 'initial-error 'initial-bound 'steps))
       (app (function/const* 'analysis/signed-general-harmonic-rate-null [])
            'ap 'gp)))}))

(def signed-vi-radius-rate-null-general-spec
  (let [gamma
        (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        source
        (function/lam
         [['steps nat]] (power-scale gamma 'steps 'initial-error))
        target
        (function/lam
         [['steps nat]]
         (error-radius (from-nnrat gamma) 'initial-error 'steps))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'analysis/signed-vi-error-radius-rate-null-general
     :universes []
     :type
     (function/forall
      [['ap nat] ['gp nat]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]]
      (signed-rate-null target modulus))
     :value
     (function/lam
      [['ap nat] ['gp nat]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]]
      (app
       (function/const* 'analysis/signed-rate-null-respects-equivalence [])
       source target modulus
       (function/lam
        [['steps nat]]
        (equiv-symmetric
         (error-radius (from-nnrat gamma) 'initial-error 'steps)
         (power-scale gamma 'steps 'initial-error)
         (app
          (function/const*
           'value/signed-vi-error-radius-is-nnrat-power-scale [])
          gamma 'initial-error 'steps)))
       (app
        (function/const* 'analysis/signed-nnrat-power-rate-null-general [])
        'ap 'gp 'initial-error
        'initial-error-nonnegative 'initial-bound)))}))

(def nnrat-transition-signed-iterate-fixed-point-converges-general-spec
  (let [gamma
        (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat gamma)
        backup
        (function/lam
         [['value value-function] ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward embedded-discount
              'value 'state 'action))
        step
        (fn [value state]
          (optimality-step
           'S 'A 'actions 'fallback backup value state))
        iterated
        (fn [steps]
          (iterate-value
           'S 'A 'actions 'fallback backup steps 'initial))
        radius
        (function/lam
         [['steps nat]]
         (error-radius embedded-discount 'initial-error 'steps))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))
        close-at
        (fn [steps state]
          (proposition/conjunction
           (sle (app (iterated steps) state)
                (sadd (app 'fixed-value state) (app radius steps)))
           (sle (app 'fixed-value state)
                (sadd (app (iterated steps) state) (app radius steps)))))
        radius-null (signed-rate-null radius modulus)
        iterate-bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (close-at 'steps 'state))]
    {:name 'value/nnrat-transition-signed-iterate-fixed-point-converges-general-rate
     :universes ['u 'v]
     :type
     (function/forall
      [['ap nat] ['gp nat]
       ['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
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
          (function/const* 'nnrat/one [])))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (seq-equiv (step 'fixed-value 'state)
                    (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]
       ['initial-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (sle (app 'initial 'state)
               (sadd (app 'fixed-value 'state) 'initial-error))
          (sle (app 'fixed-value 'state)
               (sadd (app 'initial 'state) 'initial-error))))]]
      (proposition/conjunction radius-null iterate-bounds))
     :value
     (function/lam
      [['ap nat] ['gp nat]
       ['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
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
          (function/const* 'nnrat/one [])))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (seq-equiv (step 'fixed-value 'state)
                    (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-error-nonnegative (sle signed-zero 'initial-error)]
       ['initial-bound
        (sle 'initial-error
             (from-nnrat (general-harmonic-at 'ap 'gp nat-zero)))]
       ['initial-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (sle (app 'initial 'state)
               (sadd (app 'fixed-value 'state) 'initial-error))
          (sle (app 'fixed-value 'state)
               (sadd (app 'initial 'state) 'initial-error))))]]
      (let [null-proof
            (app
             (function/const*
              'analysis/signed-vi-error-radius-rate-null-general [])
             'ap 'gp 'initial-error
             'initial-error-nonnegative 'initial-bound)
            bounds-proof
            (app
             (function/const*
              'value/nnrat-transition-signed-iterate-fixed-point-additive-radius
              [U V])
             'S 'A 'states 'actions 'transition 'reward gamma
             'fallback 'fallback-admissible 'normalized
             'fixed-value 'fixed-point 'initial 'initial-error 'initial-close)]
        (conjoin radius-null iterate-bounds null-proof bounds-proof)))}))

(def definition-specs [])
(def theorem-specs
  [signed-rate-null-from-nnrat-spec
   signed-general-harmonic-rate-null-spec
   power-scale-general-harmonic-bound-spec
   signed-power-rate-null-general-spec
   signed-vi-radius-rate-null-general-spec
   nnrat-transition-signed-iterate-fixed-point-converges-general-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(defn extend-environment [env]
  (-> env
      half-convergence/extend-environment
      (extend-specs-if-missing
       :nnrat-general-harmonic
       [general-harmonic/general-harmonic-spec
        general-harmonic/general-harmonic-null-spec])
      (extend-specs-if-missing
       :nnrat-general-contraction
       [general-contraction/general-harmonic-step-spec])
      (extend-specs-if-missing
       :signed-geometric-bridge
       [signed-bridge/from-nnrat-multiply-spec])
      (extend-specs-if-missing
       :finite-matrix-affine-nnrat-exact-rate
       [exact-rate/nnrat-power-scale-nonnegative-spec])
      (support/extend-with
       :finite-bellman-signed-value-iteration-general-converges
       theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
