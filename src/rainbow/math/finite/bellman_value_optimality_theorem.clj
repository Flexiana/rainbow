(ns rainbow.math.finite.bellman-value-optimality-theorem
  "Abstract, reduction-safe capstones for finite Bellman value iteration.

  The sequence and its error radius are parameters: no theorem statement asks
  the kernel to reduce Bellman optimality, finite argmax, or the concrete
  iterate definition.  The Bellman-specific predecessor lemmas provide the
  initial/advance and below-sequence hypotheses.  Native and axiom-free on
  D63."
  (:require [rainbow.math.finite.bellman-value-iteration-converges
             :as bellman-convergence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def type-level [:succ [:zero]])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero (function/const* 'data/zero []))
(def one (function/app (function/const* 'data/succ []) zero))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))

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

(defn- reciprocal [k]
  (function/app (function/const* 'nnrat/make []) one k))

(defn- general-harmonic [ap gp steps]
  (function/app (function/const* 'nnrat/general-harmonic []) ap gp steps))

(defn- modulus [ap]
  (function/lam
   [['k nat]]
   (function/app (function/const* 'nat/multiply []) (succ ap) 'k)))

(defn- rate-null [error modulus-value]
  (function/app (function/const* 'analysis/rate-null [])
                error modulus-value))

(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))

(defn- close-at [sequence fixed-value error steps state]
  (proposition/conjunction
   (at-most (function/app (function/app sequence steps) state)
            (add (function/app fixed-value state)
                 (function/app error steps)))
   (at-most (function/app fixed-value state)
            (add (function/app (function/app sequence steps) state)
                 (function/app error steps)))))

(def abstract-value-iteration-converges-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)
        close
        (fn [steps state]
          (close-at 'sequence 'fixed-value 'error steps state))
        close-for
        (fn [steps]
          (function/forall [['state 'S]] (close steps 'state)))
        close-motive
        (function/lam [['steps nat]] (close-for 'steps))
        threshold (modulus 'ap)
        null-result (rate-null 'error threshold)
        eventual-result
        (function/forall
         [['k nat]
          ['steps nat]
          ['late
           (function/app (function/const* 'nat/at-most [])
                         (function/app threshold 'k) 'steps)]
          ['state 'S]]
         (proposition/conjunction
          (at-most
           (function/app (function/app 'sequence 'steps) 'state)
           (add (function/app 'fixed-value 'state) (reciprocal 'k)))
          (at-most
           (function/app 'fixed-value 'state)
           (add (function/app (function/app 'sequence 'steps) 'state)
                (reciprocal 'k)))))]
    {:name 'value/nnrat-abstract-value-iteration-converges
     :universes ['u]
     :type
     (function/forall
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['sequence sequence-type]
       ['fixed-value value-function]
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
      (proposition/conjunction null-result eventual-result))
     :value
     (function/lam
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['sequence sequence-type]
       ['fixed-value value-function]
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
      (let [all-close
            (function/lam
             [['steps nat]]
             (function/app
              (function/const* 'data/Nat.rec [[:zero]])
              close-motive
              'initial-close
              (function/lam
               [['previous nat]
                ['previous-close (function/app close-motive 'previous)]]
               (function/app 'advance-close 'previous 'previous-close))
              'steps))
            null-proof
            (function/app
             (function/const* 'analysis/general-contraction-converges [])
             'ap 'gp 'error 'initial-error-bound 'error-contracts)
            eventual-proof
            (function/lam
             [['k nat]
              ['steps nat]
              ['late
               (function/app (function/const* 'nat/at-most [])
                             (function/app threshold 'k) 'steps)]
              ['state 'S]]
             (let [sequence-at
                   (function/app (function/app 'sequence 'steps) 'state)
                   fixed-at (function/app 'fixed-value 'state)
                   error-at (function/app 'error 'steps)
                   epsilon (reciprocal 'k)
                   current-close (function/app all-close 'steps 'state)
                   sequence-upper
                   (left-conjunct
                    (at-most sequence-at (add fixed-at error-at))
                    (at-most fixed-at (add sequence-at error-at))
                    current-close)
                   fixed-upper
                   (right-conjunct
                    (at-most sequence-at (add fixed-at error-at))
                    (at-most fixed-at (add sequence-at error-at))
                    current-close)
                   error-small
                   (function/app null-proof 'k 'steps 'late)
                   fixed-sum-small
                   (function/app
                    (function/const* 'nnrat/add-left-monotone [])
                    fixed-at error-at epsilon error-small)
                   sequence-sum-small
                   (function/app
                    (function/const* 'nnrat/add-left-monotone [])
                    sequence-at error-at epsilon error-small)
                   result-left
                   (function/app
                    (function/const* 'nnrat/at-most-transitive [])
                    sequence-at (add fixed-at error-at)
                    (add fixed-at epsilon)
                    sequence-upper fixed-sum-small)
                   result-right
                   (function/app
                    (function/const* 'nnrat/at-most-transitive [])
                    fixed-at (add sequence-at error-at)
                    (add sequence-at epsilon)
                    fixed-upper sequence-sum-small)]
               (function/app
                (function/const* 'proposition/conjoin [])
                (at-most sequence-at (add fixed-at epsilon))
                (at-most fixed-at (add sequence-at epsilon))
                result-left result-right)))]
        (function/app
         (function/const* 'proposition/conjoin [])
         null-result eventual-result null-proof eventual-proof)))}))

(def rate-limit-dominates-below-iterates-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)]
    {:name 'value/nnrat-rate-limit-dominates-below-iterates
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat nnrat)]
       ['threshold (function/arrow nat nat)]
       ['error-null (rate-null 'error 'threshold)]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (at-most (function/app 'lower-value 'state)
                  (function/app (function/app 'sequence 'steps) 'state)))]
       ['sequence-upper
        (function/forall
         [['steps nat] ['state 'S]]
         (at-most
          (function/app (function/app 'sequence 'steps) 'state)
          (add (function/app 'limit-value 'state)
               (function/app 'error 'steps))))]]
      (function/forall
       [['state 'S]]
       (at-most (function/app 'lower-value 'state)
                (function/app 'limit-value 'state))))
     :value
     (function/lam
      [['S type-u]
       ['sequence sequence-type]
       ['limit-value value-function]
       ['lower-value value-function]
       ['error (function/arrow nat nnrat)]
       ['threshold (function/arrow nat nat)]
       ['error-null (rate-null 'error 'threshold)]
       ['below-sequence
        (function/forall
         [['steps nat] ['state 'S]]
         (at-most (function/app 'lower-value 'state)
                  (function/app (function/app 'sequence 'steps) 'state)))]
       ['sequence-upper
        (function/forall
         [['steps nat] ['state 'S]]
         (at-most
          (function/app (function/app 'sequence 'steps) 'state)
          (add (function/app 'limit-value 'state)
               (function/app 'error 'steps))))]]
      (function/lam
       [['state 'S]]
       (function/app
        (function/const* 'analysis/nnrat-at-most-of-rate-null-upper-bounds [])
        'error 'threshold
        (function/app 'lower-value 'state)
        (function/app 'limit-value 'state)
        'error-null
        (function/lam
         [['steps nat]]
         (let [lower-at (function/app 'lower-value 'state)
               sequence-at
               (function/app (function/app 'sequence 'steps) 'state)
               target
               (add (function/app 'limit-value 'state)
                    (function/app 'error 'steps))]
           (function/app
            (function/const* 'nnrat/at-most-transitive [])
            lower-at sequence-at target
            (function/app 'below-sequence 'steps 'state)
            (function/app 'sequence-upper 'steps 'state)))))))}))

(def abstract-post-fixed-value-below-sequence-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)
        sequence-at (fn [steps] (function/app 'sequence steps))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (at-most (function/app 'value 'state)
                   (function/app (sequence-at 'steps) 'state))))]
    {:name 'value/nnrat-abstract-post-fixed-value-below-sequence
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
         (at-most (function/app 'value 'state)
                  (function/app (function/app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function]
          ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (at-most (function/app 'left 'state)
                     (function/app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (at-most
           (function/app (function/app 'operator 'left) 'state)
           (function/app (function/app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (function/app 'operator (sequence-at 'steps))))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (at-most (function/app 'value 'state)
                (function/app (sequence-at 'steps) 'state))))
     :value
     (function/lam
      [['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['value value-function]
       ['below-operator
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (function/app (function/app 'operator 'value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function]
          ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (at-most (function/app 'left 'state)
                     (function/app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (at-most
           (function/app (function/app 'operator 'left) 'state)
           (function/app (function/app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (sequence-at zero) 'value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (sequence-at (succ 'steps))
          (function/app 'operator (sequence-at 'steps))))]]
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'data/Nat.rec [[:zero]])
        motive
        (function/lam
         [['state 'S]]
         (let [value-at (function/app 'value 'state)
               zero-at (function/app (sequence-at zero) 'state)
               value-equals-zero
               (function/app
                (function/const* 'equality/symmetric [data-u])
                value-function (sequence-at zero) 'value 'sequence-zero)]
           (function/app
            (function/const* 'equality/substitution [data-u])
            value-function 'value (sequence-at zero) value-equals-zero
            (function/lam
             [['upper value-function]]
             (at-most value-at (function/app 'upper 'state)))
            (function/app (function/const* 'nnrat/at-most-reflexive [])
                          value-at))))
        (function/lam
         [['previous nat]
          ['induction-hypothesis (function/app motive 'previous)]]
         (function/lam
          [['state 'S]]
          (let [value-at (function/app 'value 'state)
                operator-value-at
                (function/app (function/app 'operator 'value) 'state)
                operator-previous
                (function/app 'operator (sequence-at 'previous))
                operator-previous-at
                (function/app operator-previous 'state)
                successor-at
                (function/app (sequence-at (succ 'previous)) 'state)
                lifted
                (function/app
                 'operator-monotone 'value (sequence-at 'previous)
                 'induction-hypothesis 'state)
                below-next-operator
                (function/app
                 (function/const* 'nnrat/at-most-transitive [])
                 value-at operator-value-at operator-previous-at
                 (function/app 'below-operator 'state) lifted)
                operator-equals-successor
                (function/app
                 (function/const* 'equality/symmetric [data-u])
                 value-function (sequence-at (succ 'previous))
                 operator-previous
                 (function/app 'sequence-successor 'previous))]
            (function/app
             (function/const* 'equality/substitution [data-u])
             value-function operator-previous
             (sequence-at (succ 'previous)) operator-equals-successor
             (function/lam
              [['upper value-function]]
              (at-most value-at (function/app 'upper 'state)))
             below-next-operator))))
        'steps)))}))

(def abstract-bellman-policy-optimality-spec
  (let [value-function (function/arrow 'S nnrat)
        sequence-type (function/arrow nat value-function)
        close
        (fn [steps state]
          (close-at 'sequence 'optimal-value 'error steps state))
        close-for
        (fn [steps]
          (function/forall [['state 'S]] (close steps 'state)))
        threshold (modulus 'ap)
        null-result (rate-null 'error threshold)
        eventual-result
        (function/forall
         [['k nat]
          ['steps nat]
          ['late
           (function/app (function/const* 'nat/at-most [])
                         (function/app threshold 'k) 'steps)]
          ['state 'S]]
         (proposition/conjunction
          (at-most
           (function/app (function/app 'sequence 'steps) 'state)
           (add (function/app 'optimal-value 'state) (reciprocal 'k)))
          (at-most
           (function/app 'optimal-value 'state)
           (add (function/app (function/app 'sequence 'steps) 'state)
                (reciprocal 'k)))))]
    {:name 'value/nnrat-abstract-bellman-policy-optimality
     :universes ['u]
     :type
     (function/forall
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['optimal-value value-function]
       ['policy-value value-function]
       ['policy-update value-function]
       ['policy-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (function/app 'policy-value 'state)
                     (function/app 'policy-update 'state)))]
       ['operator-dominates-policy
        (function/forall
         [['state 'S]]
         (at-most
          (function/app 'policy-update 'state)
          (function/app (function/app 'operator 'policy-value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function]
          ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (at-most (function/app 'left 'state)
                     (function/app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (at-most
           (function/app (function/app 'operator 'left) 'state)
           (function/app (function/app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (function/app 'sequence zero) 'policy-value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (function/app 'sequence (succ 'steps))
          (function/app 'operator (function/app 'sequence 'steps))))]
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
       (at-most (function/app 'policy-value 'state)
                (function/app 'optimal-value 'state))))
     :value
     (function/lam
      [['ap nat]
       ['gp nat]
       ['S type-u]
       ['operator (function/arrow value-function value-function)]
       ['sequence sequence-type]
       ['optimal-value value-function]
       ['policy-value value-function]
       ['policy-update value-function]
       ['policy-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent (function/app 'policy-value 'state)
                     (function/app 'policy-update 'state)))]
       ['operator-dominates-policy
        (function/forall
         [['state 'S]]
         (at-most
          (function/app 'policy-update 'state)
          (function/app (function/app 'operator 'policy-value) 'state)))]
       ['operator-monotone
        (function/forall
         [['left value-function]
          ['right value-function]
          ['ordered
           (function/forall
            [['state 'S]]
            (at-most (function/app 'left 'state)
                     (function/app 'right 'state)))]]
         (function/forall
          [['state 'S]]
          (at-most
           (function/app (function/app 'operator 'left) 'state)
           (function/app (function/app 'operator 'right) 'state))))]
       ['sequence-zero
        (function/equality data-u value-function
                           (function/app 'sequence zero) 'policy-value)]
       ['sequence-successor
        (function/forall
         [['steps nat]]
         (function/equality
          data-u value-function
          (function/app 'sequence (succ 'steps))
          (function/app 'operator (function/app 'sequence 'steps))))]
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
      (let [below-operator
            (function/lam
             [['state 'S]]
             (function/app
              (function/const* 'nnrat/at-most-transitive [])
              (function/app 'policy-value 'state)
              (function/app 'policy-update 'state)
              (function/app (function/app 'operator 'policy-value) 'state)
              (function/app
               (function/const* 'nnrat/equivalent-to-at-most [])
               (function/app 'policy-value 'state)
               (function/app 'policy-update 'state)
               (function/app 'policy-fixed-point 'state))
              (function/app 'operator-dominates-policy 'state)))
            policy-below-sequence
            (function/app
             (function/const*
              'value/nnrat-abstract-post-fixed-value-below-sequence [U])
             'S 'operator 'sequence 'policy-value below-operator
             'operator-monotone 'sequence-zero 'sequence-successor)
            converged
            (function/app
             (function/const*
              'value/nnrat-abstract-value-iteration-converges [U])
             'ap 'gp 'S 'sequence 'optimal-value 'error
             'initial-error-bound 'error-contracts
             'initial-close 'advance-close)
            eventual
            (right-conjunct null-result eventual-result converged)]
        (function/lam
         [['state 'S]]
         (function/app
          (function/const* 'nnrat/at-most-of-all-plus-reciprocal [])
          (function/app 'policy-value 'state)
          (function/app 'optimal-value 'state)
          (function/lam
           [['k nat]]
           (let [steps (function/app threshold 'k)
                 sequence-at
                 (function/app (function/app 'sequence steps) 'state)
                 optimal-at (function/app 'optimal-value 'state)
                 epsilon (reciprocal 'k)
                 late
                 (function/app (function/const* 'nat/at-most-reflexive [])
                               steps)
                 close-now (function/app eventual 'k steps late 'state)
                 iterate-upper
                 (left-conjunct
                  (at-most sequence-at (add optimal-at epsilon))
                  (at-most optimal-at (add sequence-at epsilon))
                  close-now)]
             (function/app
              (function/const* 'nnrat/at-most-transitive [])
              (function/app 'policy-value 'state)
              sequence-at (add optimal-at epsilon)
              (function/app policy-below-sequence steps 'state)
              iterate-upper)))))))}))

(def definition-specs [])
(def theorem-specs
  [abstract-value-iteration-converges-spec
   rate-limit-dominates-below-iterates-spec
   abstract-post-fixed-value-below-sequence-spec
   abstract-bellman-policy-optimality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      bellman-convergence/extend-environment
      (support/extend-with :finite-bellman-value-optimality-theorem
                           theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
