(ns rainbow.math.finite.bellman-signed-value-iteration
  "Finite-horizon signed Bellman value-iteration envelopes.

  A generic signed iterate and exact recursive error radius are defined over
  the runtime finite-action optimality operator.  A structural induction lifts
  any two-sided one-step additive contraction through every finite horizon.
  The concrete capstone instantiates that induction with an ordinary normalized
  nnrat transition kernel, arbitrary signed rewards and values, and an assumed
  signed Bellman fixed point.

  This proves finite-horizon error propagation only.  Fixed-point existence and
  convergence of the radius remain separate obligations.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-signed-transition-bridge :as bridge]
            [rainbow.math.finite.policy-evaluation :as policy-evaluation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

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

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- source-membership [level element source value]
  (app (function/const* 'finset-data/to-set [level]) element source value))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- add-respects [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime first second))
(defn- at-most-respects
  [left left-prime right right-prime left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))
(defn- optimality-step [state action actions fallback backup value current]
  (app (function/const* 'value/signed-optimality-step [U V])
       state action actions fallback backup value current))
(defn- iterate-value [state action actions fallback backup steps initial]
  (app (function/const* 'value/signed-iterate [U V])
       state action actions fallback backup steps initial))
(defn- error-radius [discount initial-error steps]
  (app (function/const* 'value/signed-vi-error-radius [])
       discount initial-error steps))
(defn- nnrat-total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- nnrat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))

(def signed-iterate-spec
  {:name 'value/signed-iterate
   :kind :definition
   :universes ['u 'v]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup
      (function/arrow (function/arrow 'S signed) 'S 'A signed)]]
    (function/arrow nat (function/arrow 'S signed)
                    (function/arrow 'S signed)))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup
      (function/arrow (function/arrow 'S signed) 'S 'A signed)]
     ['steps nat] ['initial (function/arrow 'S signed)]]
    (app
     (function/const* 'data/Nat.rec [data-u])
     (function/lam [['ignored nat]] (function/arrow 'S signed))
     'initial
     (function/lam
      [['ignored-step nat]
       ['previous (function/arrow 'S signed)]]
      (function/lam
       [['state 'S]]
       (optimality-step
        'S 'A 'actions 'fallback 'backup 'previous 'state)))
     'steps))})

(def signed-vi-error-radius-spec
  {:name 'value/signed-vi-error-radius
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow signed signed nat signed)
   :value
   (function/lam
    [['discount signed] ['initial-error signed] ['steps nat]]
    (app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] signed)
     'initial-error
     (function/lam
      [['ignored-step nat] ['previous-error signed]]
      (multiply 'discount 'previous-error))
     'steps))})

(def signed-iterate-zero-spec
  (let [value-function (function/arrow 'S signed)
        iterated
        (iterate-value
         'S 'A 'actions 'fallback 'backup nat-zero 'initial)]
    {:name 'value/signed-iterate-zero
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['initial value-function]]
      (function/equality data-u value-function iterated 'initial))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['initial value-function]]
      (app (function/const* 'equality/reflexive [data-u])
           value-function 'initial))}))

(def signed-iterate-successor-spec
  (let [value-function (function/arrow 'S signed)
        previous
        (iterate-value
         'S 'A 'actions 'fallback 'backup 'steps 'initial)
        next
        (iterate-value
         'S 'A 'actions 'fallback 'backup (succ 'steps) 'initial)
        step
        (function/lam
         [['ignored-step nat] ['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step
           'S 'A 'actions 'fallback 'backup 'value 'state)))]
    {:name 'value/signed-iterate-successor
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['steps nat] ['initial value-function]]
      (function/equality
       data-u value-function next (app step 'steps previous)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['steps nat] ['initial value-function]]
      (app (function/const* 'nat/recursor-successor-constant [U])
           value-function 'initial step 'steps))}))

(def signed-iterate-additive-radius-spec
  (let [value-function (function/arrow 'S signed)
        iterated
        (fn [steps]
          (iterate-value
           'S 'A 'actions 'fallback 'backup steps 'initial))
        radius (fn [steps] (error-radius 'discount 'initial-error steps))
        step-value
        (fn [candidate]
          (function/lam
           [['state 'S]]
           (optimality-step
            'S 'A 'actions 'fallback 'backup candidate 'state)))
        close-at
        (fn [candidate epsilon state]
          (proposition/conjunction
           (at-most (app candidate state)
                    (add (app 'fixed-value state) epsilon))
           (at-most (app 'fixed-value state)
                    (add (app candidate state) epsilon))))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (close-at (iterated 'steps) (radius 'steps) 'state)))]
    {:name 'value/signed-iterate-additive-radius
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['discount signed]
       ['fixed-value value-function]
       ['initial value-function]
       ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]
       ['advance
        (function/forall
         [['candidate value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'candidate 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at
           (step-value 'candidate)
           (multiply 'discount 'epsilon) 'state)))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (iterated 'steps) (radius 'steps) 'state)))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A signed)]
       ['discount signed]
       ['fixed-value value-function]
       ['initial value-function]
       ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]
       ['advance
        (function/forall
         [['candidate value-function]
          ['epsilon signed]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'candidate 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at
           (step-value 'candidate)
           (multiply 'discount 'epsilon) 'state)))]]
      (function/lam
       [['steps nat]]
       (app
        (function/const* 'data/Nat.rec [zero-level])
        motive
        'initial-close
        (function/lam
         [['previous-steps nat]
          ['induction-hypothesis (app motive 'previous-steps)]]
         (app 'advance
              (iterated 'previous-steps)
              (radius 'previous-steps)
              'induction-hypothesis))
        'steps)))}))

(def nnrat-transition-signed-step-fixed-point-contraction-spec
  (let [embedded-transition
        (function/lam
         [['state 'S] ['action 'A] ['next-state 'S]]
         (from-nnrat (app 'transition 'state 'action 'next-state)))
        embedded-discount (from-nnrat 'discount)
        backup
        (function/lam
         [['value (function/arrow 'S signed)]
          ['state 'S] ['action 'A]]
         (app (function/const* 'bellman/signed-action-backup [U V])
              'S 'A 'states embedded-transition 'reward embedded-discount
              'value 'state 'action))
        step
        (fn [value state]
          (optimality-step
           'S 'A 'actions 'fallback backup value state))
        contracted-error (multiply embedded-discount 'epsilon)]
    {:name 'value/nnrat-transition-signed-step-fixed-point-contraction
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
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          (function/const* 'nnrat/one [])))]
       ['fixed-value (function/arrow 'S signed)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['candidate (function/arrow 'S signed)]
       ['epsilon signed]
       ['candidate-close-left
        (function/forall
         [['state 'S]]
         (at-most (app 'candidate 'state)
                  (add (app 'fixed-value 'state) 'epsilon)))]
       ['candidate-close-right
        (function/forall
         [['state 'S]]
         (at-most (app 'fixed-value 'state)
                  (add (app 'candidate 'state) 'epsilon)))]
       ['state 'S]]
      (proposition/conjunction
       (at-most (step 'candidate 'state)
                (add (app 'fixed-value 'state) contracted-error))
       (at-most (app 'fixed-value 'state)
                (add (step 'candidate 'state) contracted-error))))
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
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          (function/const* 'nnrat/one [])))]
       ['fixed-value (function/arrow 'S signed)]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['candidate (function/arrow 'S signed)]
       ['epsilon signed]
       ['candidate-close-left
        (function/forall
         [['state 'S]]
         (at-most (app 'candidate 'state)
                  (add (app 'fixed-value 'state) 'epsilon)))]
       ['candidate-close-right
        (function/forall
         [['state 'S]]
         (at-most (app 'fixed-value 'state)
                  (add (app 'candidate 'state) 'epsilon)))]
       ['state 'S]]
      (let [candidate-step (step 'candidate 'state)
            fixed-step (step 'fixed-value 'state)
            fixed-at (app 'fixed-value 'state)
            fixed-same (app 'fixed-point 'state)
            contracted
            (app
             (function/const*
              'value/nnrat-transition-signed-optimality-step-additively-contractive
              [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'fallback-admissible 'normalized
             'candidate 'fixed-value 'epsilon
             'candidate-close-left 'candidate-close-right 'state)
            raw-left
            (at-most candidate-step
                     (add fixed-step contracted-error))
            raw-right
            (at-most fixed-step
                     (add candidate-step contracted-error))
            right-same
            (add-respects
             fixed-step fixed-at contracted-error contracted-error
             fixed-same (equiv-reflexive contracted-error))
            result-left
            (at-most-respects
             candidate-step candidate-step
             (add fixed-step contracted-error)
             (add fixed-at contracted-error)
             (equiv-reflexive candidate-step) right-same
             (left-conjunct raw-left raw-right contracted))
            result-right
            (at-most-respects
             fixed-step fixed-at
             (add candidate-step contracted-error)
             (add candidate-step contracted-error)
             fixed-same
             (equiv-reflexive (add candidate-step contracted-error))
             (right-conjunct raw-left raw-right contracted))]
        (conjoin
         (at-most candidate-step (add fixed-at contracted-error))
         (at-most fixed-at (add candidate-step contracted-error))
         result-left result-right)))}))

(def nnrat-transition-signed-iterate-fixed-point-additive-radius-spec
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
        (fn [steps]
          (error-radius embedded-discount 'initial-error steps))
        close-at
        (fn [candidate epsilon state]
          (proposition/conjunction
           (at-most (app candidate state)
                    (add (app 'fixed-value state) epsilon))
           (at-most (app 'fixed-value state)
                    (add (app candidate state) epsilon))))]
    {:name 'value/nnrat-transition-signed-iterate-fixed-point-additive-radius
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
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          (function/const* 'nnrat/one [])))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (iterated 'steps) (radius 'steps) 'state)))
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
         (nnrat-equivalent
          (nnrat-total-mass
           'S 'states (app 'transition 'state 'action))
          (function/const* 'nnrat/one [])))]
       ['fixed-value value-function]
       ['fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (step 'fixed-value 'state)
                     (app 'fixed-value 'state)))]
       ['initial value-function]
       ['initial-error signed]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]]
      (app
       (function/const* 'value/signed-iterate-additive-radius [U V])
       'S 'A 'actions 'fallback backup embedded-discount
       'fixed-value 'initial 'initial-error 'initial-close
       (function/lam
        [['candidate value-function]
         ['epsilon signed]
         ['close
          (function/forall
           [['state 'S]]
           (close-at 'candidate 'epsilon 'state))]
         ['state 'S]]
        (let [close-here (app 'close 'state)
              left-bound
              (at-most (app 'candidate 'state)
                       (add (app 'fixed-value 'state) 'epsilon))
              right-bound
              (at-most (app 'fixed-value 'state)
                       (add (app 'candidate 'state) 'epsilon))]
          (app
           (function/const*
            'value/nnrat-transition-signed-step-fixed-point-contraction
            [U V])
           'S 'A 'states 'actions 'transition 'reward 'discount
           'fallback 'fallback-admissible 'normalized
           'fixed-value 'fixed-point 'candidate 'epsilon
           (function/lam
            [['selected-state 'S]]
            (left-conjunct
             (at-most (app 'candidate 'selected-state)
                      (add (app 'fixed-value 'selected-state) 'epsilon))
             (at-most (app 'fixed-value 'selected-state)
                      (add (app 'candidate 'selected-state) 'epsilon))
             (app 'close 'selected-state)))
           (function/lam
            [['selected-state 'S]]
            (right-conjunct
             (at-most (app 'candidate 'selected-state)
                      (add (app 'fixed-value 'selected-state) 'epsilon))
             (at-most (app 'fixed-value 'selected-state)
                      (add (app 'candidate 'selected-state) 'epsilon))
             (app 'close 'selected-state)))
           'state)))))}))

(def definition-specs [signed-iterate-spec signed-vi-error-radius-spec])
(def theorem-specs
  [signed-iterate-zero-spec
   signed-iterate-successor-spec
   signed-iterate-additive-radius-spec
   nnrat-transition-signed-step-fixed-point-contraction-spec
   nnrat-transition-signed-iterate-fixed-point-additive-radius-spec])

(defn- extend-specs-if-missing [env producer specs]
  (let [missing (remove #(environment/resolve-id env (:name %)) specs)]
    (if (seq missing)
      (support/extend-with env producer missing)
      env)))

(defn extend-environment [env]
  (-> env
      bridge/extend-environment
      (extend-specs-if-missing
       :finite-policy-evaluation
       [policy-evaluation/recursor-successor-spec])
      (support/extend-with
       :finite-bellman-signed-value-iteration
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
