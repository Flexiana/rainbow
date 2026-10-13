(ns rainbow.math.finite.policy-value-dominance
  "Abstract, reduction-safe policy-improvement value dominance for finite
  nnrat MDPs.

  A fixed-policy step selects one already-fixed action at each state, so its
  monotonicity is exactly Bellman action-backup monotonicity.  Consequently a
  post-fixed value lies below every term of an abstract fixed-policy recurrence.
  If that recurrence converges to the improved policy's value, the current
  policy's value is pointwise below the improved value.  No concrete iterate or
  finite argmax occurs in a theorem statement.  Native and axiom-free on D63."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-monotone :as monotone]
            [rainbow.math.finite.bellman-value-optimality-theorem
             :as optimality-theorem]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero (function/const* 'data/zero []))
(def one (function/app (function/const* 'data/succ []) zero))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- gamma [ap gp]
  (function/app
   (function/const* 'nnrat/make [])
   (succ ap)
   (function/app (function/const* 'algebra/nat-add []) ap (succ gp))))

(defn- general-harmonic [ap gp steps]
  (function/app (function/const* 'nnrat/general-harmonic []) ap gp steps))

(defn- action-backup
  [state action states transition reward discount value current chosen]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount value current chosen))

(defn- close-at [sequence fixed-value error steps state]
  (proposition/conjunction
   (at-most (function/app (function/app sequence steps) state)
            (add (function/app fixed-value state)
                 (function/app error steps)))
   (at-most (function/app fixed-value state)
            (add (function/app (function/app sequence steps) state)
                 (function/app error steps)))))

(def fixed-policy-step-monotone-spec
  {:name 'value/nnrat-fixed-policy-step-monotone
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['policy (function/arrow 'S 'A)]
     ['lower-value (function/arrow 'S nnrat)]
     ['upper-value (function/arrow 'S nnrat)]
     ['pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'lower-value 'next-state)
                (function/app 'upper-value 'next-state)))]
     ['state 'S]]
    (at-most
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'lower-value 'state (function/app 'policy 'state))
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'upper-value 'state (function/app 'policy 'state))))
   :value
   (function/lam
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['policy (function/arrow 'S 'A)]
     ['lower-value (function/arrow 'S nnrat)]
     ['upper-value (function/arrow 'S nnrat)]
     ['pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'lower-value 'next-state)
                (function/app 'upper-value 'next-state)))]
     ['state 'S]]
    (function/app
     (function/const* 'bellman/nnrat-action-backup-monotone [U V])
     'S 'A 'states 'transition 'reward 'discount
     'lower-value 'upper-value 'pointwise
     'state (function/app 'policy 'state)))})

(def fixed-policy-post-fixed-below-sequence-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)
        sequence-at (fn [steps] (function/app 'sequence steps))
        fixed-step
        (function/lam
         [['candidate value-function]]
         (function/lam
          [['state 'S]]
          (action-backup 'S 'A 'states 'transition 'reward 'discount
                         'candidate 'state (function/app 'policy 'state))))]
    {:name 'value/nnrat-fixed-policy-post-fixed-below-sequence
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['sequence sequence-type]
       ['value value-function]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (function/app (function/app fixed-step 'value) 'state)))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (function/app fixed-step (sequence-at 'steps))))]]
      (function/forall
       [['steps nat]
        ['state 'S]]
       (at-most (function/app 'value 'state)
                (function/app (sequence-at 'steps) 'state))))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['policy (function/arrow 'S 'A)]
       ['sequence sequence-type]
       ['value value-function]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (function/app (function/app fixed-step 'value) 'state)))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (function/app fixed-step (sequence-at 'steps))))]]
      (let [step-monotone
            (function/lam
             [['lower value-function]
              ['upper value-function]
              ['ordered
               (function/forall
                [['state 'S]]
                (at-most (function/app 'lower 'state)
                         (function/app 'upper 'state)))]]
             (function/lam
              [['state 'S]]
              (function/app
               (function/const*
                'value/nnrat-fixed-policy-step-monotone [U V])
               'S 'A 'states 'transition 'reward 'discount 'policy
               'lower 'upper 'ordered 'state)))]
        (function/app
         (function/const*
          'value/nnrat-abstract-post-fixed-value-below-sequence [U])
         'S fixed-step 'sequence 'value 'below-step step-monotone
         'sequence-zero 'sequence-successor)))}))

(def policy-improvement-value-dominates-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)
        fixed-step
        (function/lam
         [['candidate value-function]]
         (function/lam
          [['state 'S]]
          (action-backup 'S 'A 'states 'transition 'reward 'discount
                         'candidate 'state
                         (function/app 'improved-policy 'state))))
        close
        (fn [steps state]
          (close-at 'sequence 'improved-value 'error steps state))
        close-for
        (fn [steps]
          (function/forall [['state 'S]] (close steps 'state)))]
    {:name 'value/nnrat-policy-improvement-value-dominates
     :universes ['u 'v]
     :type
     (function/forall
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['improved-policy (function/arrow 'S 'A)]
       ['sequence sequence-type]
       ['improved-value value-function]
       ['current-value value-function]
       ['one-step-dominance
        (function/forall
         [['state 'S]]
         (at-most
          (function/app 'current-value 'state)
          (function/app (function/app fixed-step 'current-value) 'state)))]
       ['sequence-zero
        (function/equality data-u value-function
                           (function/app 'sequence zero) 'current-value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (function/app 'sequence (succ 'steps))
          (function/app fixed-step (function/app 'sequence 'steps))))]
       ['error (function/arrow nat nnrat)]
       ['initial-error-bound
        (at-most (function/app 'error zero)
                 (general-harmonic 'ap 'gp zero))]
       ['error-contracts
        (function/forall
         [['steps nat]]
         (at-most
          (function/app 'error (succ 'steps))
          (multiply (gamma 'ap 'gp) (function/app 'error 'steps))))]
       ['initial-close (close-for zero)]
       ['advance-close
        (function/forall
         [['steps nat]
          ['previous-close (close-for 'steps)]]
         (close-for (succ 'steps)))]]
      (function/forall
       [['state 'S]]
       (at-most (function/app 'current-value 'state)
                (function/app 'improved-value 'state))))
     :value
     (function/lam
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['improved-policy (function/arrow 'S 'A)]
       ['sequence sequence-type]
       ['improved-value value-function]
       ['current-value value-function]
       ['one-step-dominance
        (function/forall
         [['state 'S]]
         (at-most
          (function/app 'current-value 'state)
          (function/app (function/app fixed-step 'current-value) 'state)))]
       ['sequence-zero
        (function/equality data-u value-function
                           (function/app 'sequence zero) 'current-value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (function/app 'sequence (succ 'steps))
          (function/app fixed-step (function/app 'sequence 'steps))))]
       ['error (function/arrow nat nnrat)]
       ['initial-error-bound
        (at-most (function/app 'error zero)
                 (general-harmonic 'ap 'gp zero))]
       ['error-contracts
        (function/forall
         [['steps nat]]
         (at-most
          (function/app 'error (succ 'steps))
          (multiply (gamma 'ap 'gp) (function/app 'error 'steps))))]
       ['initial-close (close-for zero)]
       ['advance-close
        (function/forall
         [['steps nat]
          ['previous-close (close-for 'steps)]]
         (close-for (succ 'steps)))]]
      (let [step-monotone
            (function/lam
             [['lower value-function]
              ['upper value-function]
              ['ordered
               (function/forall
                [['state 'S]]
                (at-most (function/app 'lower 'state)
                         (function/app 'upper 'state)))]]
             (function/lam
              [['state 'S]]
              (function/app
               (function/const*
                'value/nnrat-fixed-policy-step-monotone [U V])
               'S 'A 'states 'transition 'reward 'discount
               'improved-policy 'lower 'upper 'ordered 'state)))
            current-reflexive
            (function/lam
             [['state 'S]]
             (function/app
              (function/const* 'nnrat/equivalent-reflexive [])
              (function/app 'current-value 'state)))]
        (function/app
         (function/const*
          'value/nnrat-abstract-bellman-policy-optimality [U])
         'ap 'gp 'S fixed-step 'sequence 'improved-value
         'current-value 'current-value current-reflexive
         'one-step-dominance step-monotone
         'sequence-zero 'sequence-successor 'error
         'initial-error-bound 'error-contracts
         'initial-close 'advance-close)))}))

(def definition-specs [])
(def theorem-specs
  [fixed-policy-step-monotone-spec
   fixed-policy-post-fixed-below-sequence-spec
   policy-improvement-value-dominates-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Finite policy value dominance expression failed elaboration"
                {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-policy-value-dominance}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Finite policy value dominance declaration rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (let [base (-> checked-environment
                 monotone/extend-environment
                 optimality-theorem/extend-environment)]
    (reduce add-spec base (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
