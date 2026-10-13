(ns rainbow.math.finite.bellman-signed-policy-dominance
  "Dominance of admissible signed policy values by Bellman optimality.

  The concrete signed Bellman operator over normalized nnrat transitions is
  monotone. A generic induction keeps every post-fixed value below all iterates,
  while generic rate-limit lemmas turn a convergence certificate and those
  iterate bounds into pointwise dominance.

  A named normalized-transition Bellman operator and low-arity iterator keep
  the concrete policy-value dominance capstone below the kernel reduction
  budget. The earlier rejected inlined formulations remain documented as
  negative evidence. The installed lemmas are native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-signed-operator-fixed-point-convergence
             :as operator-convergence]
            [rainbow.math.finite.bellman-signed-policy-optimal
             :as policy-optimal]
            [rainbow.math.finite.bellman-signed-transition-operator
             :as transition-operator]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.rate-order :as rate-order]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
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
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- greedy-step [actions fallback backup value state]
  (app (function/const* 'value/signed-optimality-step [U V])
       'S 'A actions fallback backup value state))
(defn- iterate-value [actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       'S 'A actions fallback backup steps initial))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- named-operator [discount]
  (app
   (function/const*
    'value/nnrat-transition-signed-optimality-operator [U V])
   'S 'A 'states 'actions 'transition 'reward discount 'fallback))
(defn- operator-iterate [operator steps initial]
  (app (function/const* 'value/signed-operator-iterate [U])
       'S operator steps initial))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime same-left same-right ordered))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(defn- bellman-objects [discount]
  (let [value-function (function/arrow 'S signed)
        embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        rate (from-nnrat discount)
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
          (greedy-step 'actions 'fallback backup 'value 'state)))]
    {:value-function value-function
     :embedded-transition embedded-transition
     :rate rate :backup backup :operator operator}))

(def signed-optimality-step-monotone-spec
  (let [{:keys [value-function embedded-transition rate backup operator]}
        (bellman-objects 'discount)]
    {:name 'value/nnrat-transition-signed-optimality-step-monotone
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
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              nnrat-one))]
       ['left value-function] ['right value-function]
       ['ordered
        (function/forall
         [['state 'S]]
         (sle (app 'left 'state) (app 'right 'state)))]]
      (function/forall
       [['state 'S]]
       (sle (app operator 'left 'state)
            (app operator 'right 'state))))
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
       ['normalized
        (function/forall
         [['state 'S] ['action 'A]]
         (req (nnrat-total-mass
               'S 'states (app 'transition 'state 'action))
              nnrat-one))]
       ['left value-function] ['right value-function]
       ['ordered
        (function/forall
         [['state 'S]]
         (sle (app 'left 'state) (app 'right 'state)))]
       ['state 'S]]
      (let [zero-radius (smul rate signed-zero)
            pointwise-zero
            (function/lam
             [['next-state 'S]]
             (let [right-at (app 'right 'next-state)
                   right-plus-zero (sadd right-at signed-zero)]
               (order-respects
                (app 'left 'next-state) (app 'left 'next-state)
                right-at right-plus-zero
                (equivalent-reflexive (app 'left 'next-state))
                (equivalent-symmetric
                 right-plus-zero right-at
                 (app (function/const* 'signed/add-zero-right []) right-at))
                (app 'ordered 'next-state))))
            action-bounds
            (function/lam
             [['action 'A]
              ['member (source-membership V 'A 'actions 'action)]]
             (app
              (function/const*
               'bellman/signed-action-backup-additive-upper-bound [U V])
              'S 'A 'states embedded-transition 'reward rate
              (app (function/const* 'signed/zero-at-most-from-nnrat [])
                   'discount)
              'left 'right signed-zero pointwise-zero
              'state 'action
              (function/lam
               [['next-state 'S]]
               (app (function/const* 'signed/zero-at-most-from-nnrat [])
                    (app 'transition 'state 'action 'next-state)))
              (app
               (function/const*
                'probability/signed-total-mass-normalized-from-nnrat [U])
               'S 'states (app 'transition 'state 'action)
               (app 'normalized 'state 'action))))
            raw
            (app
             (function/const*
              'value/signed-optimality-step-additive-upper-bound [U V])
             'S 'A 'actions 'fallback 'fallback-admissible backup
             'left 'right zero-radius 'state action-bounds)
            right-step (app operator 'right 'state)
            raw-upper (sadd right-step zero-radius)
            upper-zero (sadd right-step signed-zero)
            upper-same
            (equivalent-transitive
             raw-upper upper-zero right-step
             (app (function/const* 'signed/add-respects-equivalence [])
                  right-step right-step zero-radius signed-zero
                  (equivalent-reflexive right-step)
                  (app (function/const* 'signed/multiply-zero-right []) rate))
             (app (function/const* 'signed/add-zero-right []) right-step))]
        (order-respects
         (app operator 'left 'state) (app operator 'left 'state)
         raw-upper right-step
         (equivalent-reflexive (app operator 'left 'state))
         upper-same raw)))}))

(def signed-abstract-post-fixed-below-sequence-spec
  (let [value-function (function/arrow 'S signed)
        sequence-type (function/arrow nat value-function)
        sequence-at (fn [steps] (app 'sequence steps))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (sle (app 'value 'state)
               (app (sequence-at 'steps) 'state))))]
    {:name 'value/signed-abstract-post-fixed-value-below-sequence
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['value value-function]
       ['below-operator
        (function/forall
         [['state 'S]]
         (sle (app 'value 'state)
              (app (app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function] ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (sle (app 'left 'state) (app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (sle (app (app 'operator 'left) 'state)
               (app (app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at nat-zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (app 'operator (sequence-at 'steps))))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (sle (app 'value 'state)
            (app (sequence-at 'steps) 'state))))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['value value-function]
       ['below-operator
        (function/forall
         [['state 'S]]
         (sle (app 'value 'state)
              (app (app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function] ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (sle (app 'left 'state) (app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (sle (app (app 'operator 'left) 'state)
               (app (app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at nat-zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (app 'operator (sequence-at 'steps))))]]
      (function/lam
       [['steps nat]]
       (app
        (function/const* 'data/Nat.rec [zero-level])
        motive
        (function/lam
         [['state 'S]]
         (let [value-at (app 'value 'state)
               zero-at (app (sequence-at nat-zero) 'state)
               value-equals-zero
               (app (function/const* 'equality/symmetric [data-u])
                    value-function (sequence-at nat-zero) 'value
                    'sequence-zero)]
           (app
            (function/const* 'equality/substitution [data-u])
            value-function 'value (sequence-at nat-zero) value-equals-zero
            (function/lam
             [['upper value-function]]
             (sle value-at (app 'upper 'state)))
            (order-reflexive value-at))))
        (function/lam
         [['previous nat]
          ['induction-hypothesis (app motive 'previous)]]
         (function/lam
          [['state 'S]]
          (let [value-at (app 'value 'state)
                operator-value-at (app (app 'operator 'value) 'state)
                operator-previous (app 'operator (sequence-at 'previous))
                operator-previous-at (app operator-previous 'state)
                lifted
                (app 'operator-monotone
                     'value (sequence-at 'previous)
                     'induction-hypothesis 'state)
                below-next-operator
                (order-transitive
                 value-at operator-value-at operator-previous-at
                 (app 'below-operator 'state) lifted)
                operator-equals-successor
                (app
                 (function/const* 'equality/symmetric [data-u])
                 value-function (sequence-at (succ 'previous))
                 operator-previous
                 (app 'sequence-successor 'previous))]
            (app
             (function/const* 'equality/substitution [data-u])
             value-function operator-previous
             (sequence-at (succ 'previous)) operator-equals-successor
             (function/lam
              [['upper value-function]]
              (sle value-at (app 'upper 'state)))
             below-next-operator))))
        'steps)))}))

(def signed-policy-fixed-point-below-optimality-step-spec
  (let [value-function (function/arrow 'S signed)
        policy-backup (app 'backup 'value 'state (app 'policy 'state))
        optimum (greedy-step 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/signed-policy-fixed-point-below-optimality-step
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['value value-function]
       ['policy (function/arrow 'S 'A)]
       ['policy-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'policy 'state)))]
       ['policy-fixed
        (function/forall
         [['state 'S]]
         (veq (app 'backup 'value 'state (app 'policy 'state))
              (app 'value 'state)))]
       ['state 'S]]
      (sle (app 'value 'state) optimum))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['value value-function]
       ['policy (function/arrow 'S 'A)]
       ['policy-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions (app 'policy 'state)))]
       ['policy-fixed
        (function/forall
         [['state 'S]]
         (veq (app 'backup 'value 'state (app 'policy 'state))
              (app 'value 'state)))]
       ['state 'S]]
      (let [value-at (app 'value 'state)
            value-below-backup
            (app
             (function/const* 'signed/equivalent-to-at-most [])
             value-at policy-backup
             (equivalent-symmetric
              policy-backup value-at (app 'policy-fixed 'state)))
            backup-below-optimum
            (app
             (function/const*
              'value/signed-optimality-step-dominates-policy [U V])
             'S 'A 'actions 'fallback 'backup 'value
             'policy 'policy-admissible 'state)]
        (order-transitive
         value-at policy-backup optimum
         value-below-backup backup-below-optimum)))}))

(def signed-rate-limit-dominates-below-iterates-spec
  (let [value-function (function/arrow 'S signed)
        sequence-type (function/arrow nat value-function)]
    {:name 'value/signed-rate-limit-dominates-below-iterates
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['error-null (signed-rate-null 'error 'modulus)]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app 'lower-value 'state)
              (app (app 'sequence 'steps) 'state)))]
       ['sequence-upper
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app (app 'sequence 'steps) 'state)
              (sadd (app 'limit-value 'state)
                    (app 'error 'steps))))]]
      (function/forall
       [['state 'S]]
       (sle (app 'lower-value 'state)
            (app 'limit-value 'state))))
     :value
     (function/lam
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['error-null (signed-rate-null 'error 'modulus)]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app 'lower-value 'state)
              (app (app 'sequence 'steps) 'state)))]
       ['sequence-upper
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app (app 'sequence 'steps) 'state)
              (sadd (app 'limit-value 'state)
                    (app 'error 'steps))))]]
      (function/lam
       [['state 'S]]
       (app
        (function/const*
         'analysis/signed-at-most-of-rate-null-upper-bounds [])
        'error 'modulus
        (app 'lower-value 'state) (app 'limit-value 'state)
        'error-null
        (function/lam
         [['steps nat]]
         (order-transitive
          (app 'lower-value 'state)
          (app (app 'sequence 'steps) 'state)
          (sadd (app 'limit-value 'state) (app 'error 'steps))
          (app 'below-sequence 'steps 'state)
          (app 'sequence-upper 'steps 'state))))))}))

(def signed-convergence-certificate-dominates-below-value-spec
  (let [value-function (function/arrow 'S signed)
        sequence-type (function/arrow nat value-function)
        bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (proposition/conjunction
          (sle (app (app 'sequence 'steps) 'state)
               (sadd (app 'limit-value 'state) (app 'error 'steps)))
          (sle (app 'limit-value 'state)
               (sadd (app (app 'sequence 'steps) 'state)
                     (app 'error 'steps)))))
        converged
        (proposition/conjunction
         (signed-rate-null 'error 'modulus) bounds)]
    {:name 'value/signed-convergence-certificate-dominates-below-value
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['converged converged]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app 'lower-value 'state)
              (app (app 'sequence 'steps) 'state)))]]
      (function/forall
       [['state 'S]]
       (sle (app 'lower-value 'state) (app 'limit-value 'state))))
     :value
     (function/lam
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat signed)]
       ['modulus (function/arrow nat nat)]
       ['converged converged]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (sle (app 'lower-value 'state)
              (app (app 'sequence 'steps) 'state)))]]
      (let [null-proof
            (left-conjunct
             (signed-rate-null 'error 'modulus) bounds 'converged)
            bounds-proof
            (right-conjunct
             (signed-rate-null 'error 'modulus) bounds 'converged)]
        (app
         (function/const*
          'value/signed-rate-limit-dominates-below-iterates [U])
         'S 'sequence 'limit-value 'lower-value 'error 'modulus
         null-proof 'below-sequence
         (function/lam
          [['steps nat] ['state 'S]]
          (left-conjunct
           (sle (app (app 'sequence 'steps) 'state)
                (sadd (app 'limit-value 'state) (app 'error 'steps)))
           (sle (app 'limit-value 'state)
                (sadd (app (app 'sequence 'steps) 'state)
                      (app 'error 'steps)))
           (app bounds-proof 'steps 'state))))))}))

(def signed-post-fixed-below-operator-iterate-spec
  (let [value-function (function/arrow 'S signed)
        sequence
        (function/lam
         [['steps nat]] (operator-iterate 'operator 'steps 'value))]
    {:name 'value/signed-post-fixed-value-below-operator-iterate
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['value value-function]
       ['below-operator
        (function/forall
         [['state 'S]]
         (sle (app 'value 'state)
              (app (app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function] ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (sle (app 'left 'state) (app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (sle (app (app 'operator 'left) 'state)
               (app (app 'operator 'right) 'state))))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (sle (app 'value 'state)
            (app (app sequence 'steps) 'state))))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['value value-function]
       ['below-operator
        (function/forall
         [['state 'S]]
         (sle (app 'value 'state)
              (app (app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function] ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (sle (app 'left 'state) (app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (sle (app (app 'operator 'left) 'state)
               (app (app 'operator 'right) 'state))))]]
      (app
       (function/const*
        'value/signed-abstract-post-fixed-value-below-sequence [U])
       'S 'operator sequence 'value 'below-operator 'operator-monotone
       (app (function/const* 'value/signed-operator-iterate-zero [U])
            'S 'operator 'value)
       (function/lam
        [['steps nat]]
        (app (function/const* 'value/signed-operator-iterate-successor [U])
             'S 'operator 'steps 'value))))}))

(defn- concrete-model-binders [discount]
  [['S type-u] ['A type-v]
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
     (req (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          nnrat-one))]])

(def named-signed-optimality-operator-monotone-spec
  (let [value-function (function/arrow 'S signed)
        named (named-operator 'discount)
        {:keys [operator]} (bellman-objects 'discount)]
    {:name 'value/nnrat-transition-signed-optimality-operator-monotone
     :universes ['u 'v]
     :type
     (function/forall
      (into
       [['discount nnrat]]
       (concat
        (concrete-model-binders 'discount)
        [['left value-function] ['right value-function]
         ['ordered
          (function/forall
           [['state 'S]]
           (sle (app 'left 'state) (app 'right 'state)))]]))
      (function/forall
       [['state 'S]]
       (sle (app named 'left 'state) (app named 'right 'state))))
     :value
     (function/lam
      (into
       [['discount nnrat]]
       (concat
        (concrete-model-binders 'discount)
        [['left value-function] ['right value-function]
         ['ordered
          (function/forall
           [['state 'S]]
           (sle (app 'left 'state) (app 'right 'state)))]
         ['state 'S]]))
      (let [raw-left (app operator 'left 'state)
            raw-right (app operator 'right 'state)
            named-left (app named 'left 'state)
            named-right (app named 'right 'state)
            raw-order
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-step-monotone [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'fallback-admissible 'normalized
             'left 'right 'ordered 'state)
            named-left-same
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-operator-unfold [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount 'fallback
             'left 'state)
            named-right-same
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-operator-unfold [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount 'fallback
             'right 'state)]
        (order-respects
         raw-left named-left raw-right named-right
         (equivalent-symmetric named-left raw-left named-left-same)
         (equivalent-symmetric named-right raw-right named-right-same)
         raw-order)))}))

(def named-policy-fixed-point-below-optimality-operator-spec
  (let [value-function (function/arrow 'S signed)
        named (named-operator 'discount)
        {:keys [backup operator]} (bellman-objects 'discount)]
    {:name
     'value/nnrat-transition-signed-policy-fixed-point-below-optimality-operator
     :universes ['u 'v]
     :type
     (function/forall
      (into
       [['discount nnrat]]
       (concat
        (concrete-model-binders 'discount)
        [['value value-function]
         ['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'policy 'state)))]
         ['policy-fixed
          (function/forall
           [['state 'S]]
           (veq (app backup 'value 'state (app 'policy 'state))
                (app 'value 'state)))]]))
      (function/forall
       [['state 'S]]
       (sle (app 'value 'state) (app named 'value 'state))))
     :value
     (function/lam
      (into
       [['discount nnrat]]
       (concat
        (concrete-model-binders 'discount)
        [['value value-function]
         ['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'policy 'state)))]
         ['policy-fixed
          (function/forall
           [['state 'S]]
           (veq (app backup 'value 'state (app 'policy 'state))
                (app 'value 'state)))]
         ['state 'S]]))
      (let [value-at (app 'value 'state)
            raw-at (app operator 'value 'state)
            named-at (app named 'value 'state)
            below-raw
            (app
             (function/const*
              'value/signed-policy-fixed-point-below-optimality-step [U V])
             'S 'A 'actions 'fallback backup 'value
             'policy 'policy-admissible 'policy-fixed 'state)
            named-same
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-operator-unfold [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount 'fallback
             'value 'state)]
        (order-respects
         value-at value-at raw-at named-at
         (equivalent-reflexive value-at)
         (equivalent-symmetric named-at raw-at named-same)
         below-raw)))}))

(def concrete-policy-value-below-operator-iterate-spec
  (let [value-function (function/arrow 'S signed)
        operator (named-operator 'discount)
        sequence
        (function/lam
         [['steps nat]] (operator-iterate operator 'steps 'policy-value))]
    {:name
     'value/nnrat-transition-signed-policy-value-below-optimality-operator-iterate
     :universes ['u 'v]
     :type
     (function/forall
      (into
       [['discount nnrat]]
       (concat
        (concrete-model-binders 'discount)
        [['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'policy 'state)))]
         ['policy-value value-function]
         ['policy-fixed
          (let [{:keys [backup]} (bellman-objects 'discount)]
            (function/forall
             [['state 'S]]
             (veq (app backup 'policy-value 'state (app 'policy 'state))
                  (app 'policy-value 'state))))]]))
      (function/forall
       [['steps nat] ['state 'S]]
       (sle (app 'policy-value 'state)
            (app (app sequence 'steps) 'state))))
     :value
     (let [{:keys [backup]} (bellman-objects 'discount)]
       (function/lam
        (into
         [['discount nnrat]]
         (concat
          (concrete-model-binders 'discount)
          [['policy (function/arrow 'S 'A)]
           ['policy-admissible
            (function/forall
             [['state 'S]]
             (source-membership V 'A 'actions (app 'policy 'state)))]
           ['policy-value value-function]
           ['policy-fixed
            (function/forall
             [['state 'S]]
             (veq (app backup 'policy-value 'state (app 'policy 'state))
                  (app 'policy-value 'state)))]]))
        (app
         (function/const*
          'value/signed-post-fixed-value-below-operator-iterate [U])
         'S operator 'policy-value
         (app
          (function/const*
           'value/nnrat-transition-signed-policy-fixed-point-below-optimality-operator
           [U V])
          'discount 'S 'A 'states 'actions 'transition 'reward 'fallback
          'fallback-admissible 'normalized 'policy-value
          'policy 'policy-admissible 'policy-fixed)
         (function/lam
          [['left value-function] ['right value-function]
           ['ordered
            (function/forall
             [['state 'S]]
             (sle (app 'left 'state) (app 'right 'state)))]
           ['state 'S]]
          (app
           (function/const*
            'value/nnrat-transition-signed-optimality-operator-monotone [U V])
           'discount 'S 'A 'states 'actions 'transition 'reward 'fallback
           'fallback-admissible 'normalized
           'left 'right 'ordered 'state)))))}))

(def concrete-policy-value-below-optimality-fixed-point-named-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        discount (from-nnrat gamma)
        value-function (function/arrow 'S signed)
        operator (named-operator gamma)
        {:keys [backup]} (bellman-objects gamma)
        sequence
        (function/lam
         [['steps nat]] (operator-iterate operator 'steps 'policy-value))
        radius
        (function/lam
         [['steps nat]] (error-radius discount 'initial-error 'steps))
        modulus
        (function/lam [['index nat]] (nmul (succ 'ap) 'index))
        binders
        (into
         [['ap nat] ['gp nat]]
         (concat
          (concrete-model-binders gamma)
          [['fixed-value value-function]
           ['fixed-point
            (function/forall
             [['state 'S]]
             (veq (app operator 'fixed-value 'state)
                  (app 'fixed-value 'state)))]
           ['policy (function/arrow 'S 'A)]
           ['policy-admissible
            (function/forall
             [['state 'S]]
             (source-membership V 'A 'actions (app 'policy 'state)))]
           ['policy-value value-function]
           ['policy-fixed
            (function/forall
             [['state 'S]]
             (veq (app backup 'policy-value 'state (app 'policy 'state))
                  (app 'policy-value 'state)))]
           ['initial-error signed]
           ['initial-error-nonnegative (sle signed-zero 'initial-error)]
           ['initial-bound
            (sle 'initial-error
                 (from-nnrat
                  (app (function/const* 'nnrat/general-harmonic [])
                       'ap 'gp nat-zero)))]
           ['initial-close
            (function/forall
             [['state 'S]]
             (proposition/conjunction
              (sle (app 'policy-value 'state)
                   (sadd (app 'fixed-value 'state) 'initial-error))
              (sle (app 'fixed-value 'state)
                   (sadd (app 'policy-value 'state) 'initial-error))))]]))]
    {:name
     'value/nnrat-transition-signed-policy-value-below-optimality-fixed-point
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (sle (app 'policy-value 'state) (app 'fixed-value 'state))))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'value/signed-convergence-certificate-dominates-below-value [U])
       'S sequence 'fixed-value 'policy-value radius modulus
       (app
        (function/const*
         'value/signed-contractive-operator-iterate-fixed-point-converges-general-rate
         [U])
        'ap 'gp 'S operator 'fixed-value 'fixed-point
        'policy-value 'initial-error
        'initial-error-nonnegative 'initial-bound 'initial-close
        (function/lam
         [['left value-function] ['right value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]]
            (proposition/conjunction
             (sle (app 'left 'state)
                  (sadd (app 'right 'state) 'epsilon))
             (sle (app 'right 'state)
                  (sadd (app 'left 'state) 'epsilon))))]
          ['state 'S]]
         (app
          (function/const*
           'value/nnrat-transition-signed-optimality-operator-additively-contractive
           [U V])
          'S 'A 'states 'actions 'transition 'reward gamma 'fallback
          'fallback-admissible 'normalized
          'left 'right 'epsilon 'close 'state)))
       (app
        (function/const*
         'value/nnrat-transition-signed-policy-value-below-optimality-operator-iterate
         [U V])
        gamma 'S 'A 'states 'actions 'transition 'reward 'fallback
        'fallback-admissible 'normalized
        'policy 'policy-admissible 'policy-value 'policy-fixed)))}))

(comment
  ;; Negative result, 2026-09-02. Neither declaration is installed or claimed.
  ;; The concrete iterate wrapper exhausted the kernel beta budget. Inlining
  ;; its already checked generic induction into the final capstone moved the
  ;; failure to the capstone's delta budget, even after the convergence side was
  ;; factored through signed-convergence-certificate-dominates-below-value-spec.
(def signed-post-fixed-value-below-bellman-iterate-spec
  (let [{:keys [value-function backup operator]} (bellman-objects 'discount)
        iterated
        (function/lam
         [['steps nat]]
         (iterate-value 'actions 'fallback backup 'steps 'value))
        binders
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
         ['normalized
          (function/forall
           [['state 'S] ['action 'A]]
           (req (nnrat-total-mass
                 'S 'states (app 'transition 'state 'action))
                nnrat-one))]
         ['value value-function]
         ['below-operator
          (function/forall
           [['state 'S]]
           (sle (app 'value 'state) (app operator 'value 'state)))]]]
    {:name 'value/nnrat-transition-signed-post-fixed-value-below-iterate
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['steps nat] ['state 'S]]
       (sle (app 'value 'state)
            (app (app iterated 'steps) 'state))))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'value/signed-abstract-post-fixed-value-below-sequence [U])
       'S operator iterated 'value 'below-operator
       (function/lam
        [['left value-function] ['right value-function]
         ['ordered
          (function/forall
           [['state 'S]]
           (sle (app 'left 'state) (app 'right 'state)))]]
        (app
         (function/const*
          'value/nnrat-transition-signed-optimality-step-monotone [U V])
         'S 'A 'states 'actions 'transition 'reward 'discount
         'fallback 'fallback-admissible 'normalized
         'left 'right 'ordered))
       (app (function/const* 'value/signed-iterate-zero [U V])
            'S 'A 'actions 'fallback backup 'value)
       (function/lam
        [['steps nat]]
        (app (function/const* 'value/signed-iterate-successor [U V])
             'S 'A 'actions 'fallback backup 'steps 'value))))}))

(def signed-policy-value-below-optimality-fixed-point-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        {:keys [value-function backup operator]} (bellman-objects gamma)
        iterated
        (function/lam
         [['steps nat]]
         (iterate-value 'actions 'fallback backup 'steps 'policy-value))
        radius
        (function/lam
         [['steps nat]]
         (error-radius (from-nnrat gamma) 'initial-error 'steps))
        modulus
        (function/lam
         [['k nat]] (nmul (succ 'ap) 'k))
        binders
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
           (req (nnrat-total-mass
                 'S 'states (app 'transition 'state 'action))
                nnrat-one))]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (veq (app operator 'fixed-value 'state)
                (app 'fixed-value 'state)))]
         ['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions (app 'policy 'state)))]
         ['policy-value value-function]
         ['policy-fixed
          (function/forall
           [['state 'S]]
           (veq (app backup 'policy-value 'state (app 'policy 'state))
                (app 'policy-value 'state)))]
         ['initial-error signed]
         ['initial-error-nonnegative (sle signed-zero 'initial-error)]
         ['initial-bound
          (sle 'initial-error
               (from-nnrat
                (app (function/const* 'nnrat/general-harmonic [])
                     'ap 'gp nat-zero)))]
         ['initial-close
          (function/forall
           [['state 'S]]
           (proposition/conjunction
            (sle (app 'policy-value 'state)
                 (sadd (app 'fixed-value 'state) 'initial-error))
            (sle (app 'fixed-value 'state)
                 (sadd (app 'policy-value 'state) 'initial-error))))]]]
    {:name 'value/nnrat-transition-signed-policy-value-below-optimality-fixed-point
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (sle (app 'policy-value 'state) (app 'fixed-value 'state))))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'value/signed-convergence-certificate-dominates-below-value [U])
       'S iterated 'fixed-value 'policy-value radius modulus
       (app
        (function/const*
         'value/nnrat-transition-signed-iterate-fixed-point-converges-general-rate
         [U V])
        'ap 'gp 'S 'A 'states 'actions 'transition 'reward
        'fallback 'fallback-admissible 'normalized
        'fixed-value 'fixed-point 'policy-value
        'initial-error 'initial-error-nonnegative
        'initial-bound 'initial-close)
       (app
        (function/const*
         'value/signed-abstract-post-fixed-value-below-sequence [U])
        'S operator iterated 'policy-value
        (function/lam
         [['state 'S]]
         (app
          (function/const*
           'value/signed-policy-fixed-point-below-optimality-step [U V])
          'S 'A 'actions 'fallback backup 'policy-value
          'policy 'policy-admissible 'policy-fixed 'state))
        (function/lam
         [['left value-function] ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (sle (app 'left 'state) (app 'right 'state)))]]
         (app
          (function/const*
           'value/nnrat-transition-signed-optimality-step-monotone [U V])
          'S 'A 'states 'actions 'transition 'reward gamma
          'fallback 'fallback-admissible 'normalized
          'left 'right 'ordered))
        (app (function/const* 'value/signed-iterate-zero [U V])
             'S 'A 'actions 'fallback backup 'policy-value)
        (function/lam
         [['steps nat]]
         (app (function/const* 'value/signed-iterate-successor [U V])
              'S 'A 'actions 'fallback backup
              'steps 'policy-value)))))})))

(def definition-specs [])
(def theorem-specs
  [signed-optimality-step-monotone-spec
   signed-abstract-post-fixed-below-sequence-spec
   signed-policy-fixed-point-below-optimality-step-spec
   signed-rate-limit-dominates-below-iterates-spec
   signed-convergence-certificate-dominates-below-value-spec
   signed-post-fixed-below-operator-iterate-spec
   named-signed-optimality-operator-monotone-spec
   named-policy-fixed-point-below-optimality-operator-spec
   concrete-policy-value-below-operator-iterate-spec
   concrete-policy-value-below-optimality-fixed-point-named-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-signed-policy-optimal rainbow.math.rational.signed.rate-order rainbow.math.finite.bellman-signed-operator-fixed-point-convergence rainbow.math.finite.bellman-signed-transition-operator])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-policy-dominance theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-policy-dominance))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
