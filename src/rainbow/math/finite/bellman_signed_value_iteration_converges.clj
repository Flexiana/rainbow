(ns rainbow.math.finite.bellman-signed-value-iteration-converges
  "Rate-null convergence certificate for signed Bellman value iteration.

  The signed Bellman error-radius recurrence is pointwise equivalent to the
  established exact `signed/nnrat-power-scale`.  For an nnrat discount at most
  one half and an initial signed error between zero and one, the existing
  identity-modulus signed rate-null theorem therefore applies.  Combining that
  certificate with the finite-horizon Bellman envelope yields an explicit
  convergence package around an assumed fixed point.

  The one-half restriction comes from the currently available signed geometric
  library.  Fixed-point existence remains a premise.  Native, kernel-checked,
  and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-value-iteration
             :as value-iteration]
            [rainbow.math.linear.matrix.affine-nnrat-exact-rate-null
             :as exact-null]
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
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- nnrat-at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- nnrat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equiv-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- power-scale [discount steps initial-error]
  (app (function/const* 'signed/nnrat-power-scale [])
       discount steps initial-error))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null [])
       sequence modulus))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- iterate-value [state action actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       state action actions fallback backup steps initial))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))

(def radius-is-nnrat-power-scale-spec
  {:name 'value/signed-vi-error-radius-is-nnrat-power-scale
   :universes []
   :type
   (function/forall
    [['discount nnrat] ['initial-error signed] ['steps nat]]
    (equivalent
     (error-radius (from-nnrat 'discount) 'initial-error 'steps)
     (power-scale 'discount 'steps 'initial-error)))
   :value
   (function/lam
    [['discount nnrat] ['initial-error signed] ['steps nat]]
    (equiv-reflexive
     (error-radius (from-nnrat 'discount) 'initial-error 'steps)))})

(def radius-rate-null-spec
  (let [radius-sequence
        (function/lam
         [['steps nat]]
         (error-radius (from-nnrat 'discount) 'initial-error 'steps))
        power-sequence
        (function/lam
         [['steps nat]]
         (power-scale 'discount 'steps 'initial-error))
        modulus (function/lam [['index nat]] 'index)]
    {:name 'analysis/signed-vi-error-radius-rate-null-of-at-most-half
     :universes []
     :type
     (function/forall
      [['discount nnrat]
       ['discount-at-most-half (nnrat-at-most 'discount nnrat-half)]
       ['initial-error signed]
       ['initial-error-nonnegative (at-most signed-zero 'initial-error)]
       ['initial-error-at-most-one (at-most 'initial-error signed-one)]]
      (signed-rate-null radius-sequence modulus))
     :value
     (function/lam
      [['discount nnrat]
       ['discount-at-most-half (nnrat-at-most 'discount nnrat-half)]
       ['initial-error signed]
       ['initial-error-nonnegative (at-most signed-zero 'initial-error)]
       ['initial-error-at-most-one (at-most 'initial-error signed-one)]]
      (app
       (function/const* 'analysis/signed-rate-null-respects-equivalence [])
       power-sequence radius-sequence modulus
       (function/lam
        [['steps nat]]
        (equiv-symmetric
         (error-radius (from-nnrat 'discount) 'initial-error 'steps)
         (power-scale 'discount 'steps 'initial-error)
         (app
          (function/const*
           'value/signed-vi-error-radius-is-nnrat-power-scale [])
          'discount 'initial-error 'steps)))
       (app
        (function/const*
         'analysis/signed-nnrat-power-rate-null-of-at-most-half [])
        'discount 'discount-at-most-half
        'initial-error 'initial-error-nonnegative
        'initial-error-at-most-one)))}))

(def nnrat-transition-signed-iterate-fixed-point-converges-spec
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat 'discount)
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
        modulus (function/lam [['index nat]] 'index)
        close-at
        (fn [steps state]
          (proposition/conjunction
           (at-most (app (iterated steps) state)
                    (add (app 'fixed-value state) (app radius steps)))
           (at-most (app 'fixed-value state)
                    (add (app (iterated steps) state) (app radius steps)))))
        radius-null (signed-rate-null radius modulus)
        iterate-bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (close-at 'steps 'state))]
    {:name 'value/nnrat-transition-signed-iterate-fixed-point-converges-at-most-half
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['discount-at-most-half (nnrat-at-most 'discount nnrat-half)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-error-nonnegative (at-most signed-zero 'initial-error)]
       ['initial-error-at-most-one (at-most 'initial-error signed-one)]
       ['initial-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (at-most (app 'initial 'state)
                   (add (app 'fixed-value 'state) 'initial-error))
          (at-most (app 'fixed-value 'state)
                   (add (app 'initial 'state) 'initial-error))))]]
      (proposition/conjunction radius-null iterate-bounds))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount nnrat]
       ['discount-at-most-half (nnrat-at-most 'discount nnrat-half)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'fallback 'state)))]
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-error-nonnegative (at-most signed-zero 'initial-error)]
       ['initial-error-at-most-one (at-most 'initial-error signed-one)]
       ['initial-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (at-most (app 'initial 'state)
                   (add (app 'fixed-value 'state) 'initial-error))
          (at-most (app 'fixed-value 'state)
                   (add (app 'initial 'state) 'initial-error))))]]
      (let [null-proof
            (app
             (function/const*
              'analysis/signed-vi-error-radius-rate-null-of-at-most-half [])
             'discount 'discount-at-most-half
             'initial-error 'initial-error-nonnegative
             'initial-error-at-most-one)
            bounds-proof
            (app
             (function/const*
              'value/nnrat-transition-signed-iterate-fixed-point-additive-radius
              [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'fallback-admissible 'normalized
             'fixed-value 'fixed-point 'initial 'initial-error 'initial-close)]
        (conjoin radius-null iterate-bounds null-proof bounds-proof)))}))

(def definition-specs [])
(def theorem-specs
  [radius-is-nnrat-power-scale-spec
   radius-rate-null-spec
   nnrat-transition-signed-iterate-fixed-point-converges-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-nnrat-exact-rate-null rainbow.math.finite.bellman-signed-value-iteration])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-value-iteration-converges theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-value-iteration-converges))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
