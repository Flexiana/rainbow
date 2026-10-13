(ns rainbow.math.finite.bellman-signed-action-backup
  "Concrete signed Bellman action backups and their additive contraction.

  The backup is reward + discount * expectation over a finite state carrier.
  Rewards and values may be arbitrary exact signed rationals.  Transition
  weights and discount are signed rationals with explicit nonnegativity; each
  transition row carries explicit total-mass-one evidence.

  A normalized row transports two-sided pointwise epsilon-closeness to
  discount*epsilon-closeness of the corresponding action backups.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.signed-expectation :as expectation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.add-associative :as associative]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [level element]
  (app (function/const* 'finset-data/Finset [level]) element))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- total-mass [element source mass]
  (app (function/const* 'probability/signed-total-mass [U])
       element source mass))
(defn- finite-expectation [element source mass value]
  (app (function/const* 'probability/signed-expectation [U])
       element source mass value))
(defn- action-backup
  [state action states transition reward discount value current chosen]
  (app (function/const* 'bellman/signed-action-backup [U V])
       state action states transition reward discount value current chosen))
(defn- equiv-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equiv-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- equiv-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- add-respects [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-respects-equivalence [])
       left left-prime right right-prime first second))

(def action-backup-spec
  {:name 'bellman/signed-action-backup
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S signed)]
     ['reward (function/arrow 'S 'A signed)]
     ['discount signed] ['value (function/arrow 'S signed)]]
    (function/arrow 'S 'A signed))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S signed)]
     ['reward (function/arrow 'S 'A signed)]
     ['discount signed] ['value (function/arrow 'S signed)]
     ['state 'S] ['action 'A]]
    (add
     (app 'reward 'state 'action)
     (multiply
      'discount
      (finite-expectation
       'S 'states (app 'transition 'state 'action) 'value))))})

(def action-backup-unfold-spec
  (let [backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'value 'state 'action)
        unfolded
        (add
         (app 'reward 'state 'action)
         (multiply
          'discount
          (finite-expectation
           'S 'states (app 'transition 'state 'action) 'value)))]
    {:name 'bellman/signed-action-backup-unfold
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed] ['value (function/arrow 'S signed)]
       ['state 'S] ['action 'A]]
      (function/equality [:succ zero-level] signed backup unfolded))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed] ['value (function/arrow 'S signed)]
       ['state 'S] ['action 'A]]
      (app (function/const* 'equality/reflexive [[:succ zero-level]])
           signed backup))}))

(def action-backup-additive-upper-bound-spec
  {:name 'bellman/signed-action-backup-additive-upper-bound
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S signed)]
     ['reward (function/arrow 'S 'A signed)]
     ['discount signed]
     ['discount-nonnegative (at-most signed-zero 'discount)]
     ['left-value (function/arrow 'S signed)]
     ['right-value (function/arrow 'S signed)]
     ['epsilon signed]
     ['left-pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (app 'left-value 'next-state)
                (add (app 'right-value 'next-state) 'epsilon)))]
     ['state 'S] ['action 'A]
     ['row-nonnegative
      (function/forall
       [['next-state 'S]]
       (at-most signed-zero
                (app 'transition 'state 'action 'next-state)))]
     ['row-normalized
      (equivalent
       (total-mass 'S 'states (app 'transition 'state 'action))
       signed-one)]]
    (at-most
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'left-value 'state 'action)
     (add
      (action-backup 'S 'A 'states 'transition 'reward 'discount
                     'right-value 'state 'action)
      (multiply 'discount 'epsilon))))
   :value
   (function/lam
    [['S type-u] ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S signed)]
     ['reward (function/arrow 'S 'A signed)]
     ['discount signed]
     ['discount-nonnegative (at-most signed-zero 'discount)]
     ['left-value (function/arrow 'S signed)]
     ['right-value (function/arrow 'S signed)]
     ['epsilon signed]
     ['left-pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (app 'left-value 'next-state)
                (add (app 'right-value 'next-state) 'epsilon)))]
     ['state 'S] ['action 'A]
     ['row-nonnegative
      (function/forall
       [['next-state 'S]]
       (at-most signed-zero
                (app 'transition 'state 'action 'next-state)))]
     ['row-normalized
      (equivalent
       (total-mass 'S 'states (app 'transition 'state 'action))
       signed-one)]]
    (let [mass (app 'transition 'state 'action)
          reward-value (app 'reward 'state 'action)
          left-expectation
          (finite-expectation 'S 'states mass 'left-value)
          right-expectation
          (finite-expectation 'S 'states mass 'right-value)
          discounted-left (multiply 'discount left-expectation)
          discounted-right (multiply 'discount right-expectation)
          discounted-epsilon (multiply 'discount 'epsilon)
          discounted-shift
          (multiply 'discount (add right-expectation 'epsilon))
          unfolded-left (add reward-value discounted-left)
          ordered-upper (add reward-value discounted-shift)
          target (add (add reward-value discounted-right)
                      discounted-epsilon)
          expectation-bound
          (app
           (function/const*
            'probability/signed-expectation-additive-upper-bound-normalized
            [U])
           'S 'states mass 'row-nonnegative 'row-normalized
           'left-value 'right-value 'epsilon 'left-pointwise)
          discounted-bound
          (app (function/const* 'signed/multiply-left-monotone [])
               'discount left-expectation
               (add right-expectation 'epsilon)
               'discount-nonnegative expectation-bound)
          reward-bound
          (app (function/const* 'signed/add-left-monotone [])
               discounted-left discounted-shift reward-value discounted-bound)
          associate-target
          (app (function/const* 'signed/add-associative [])
               reward-value discounted-right discounted-epsilon)
          distribute-discount
          (app
           (function/const* 'signed/multiply-distributes-add-left [])
           'discount right-expectation 'epsilon)
          collect-discount
          (add-respects
           reward-value reward-value
           (add discounted-right discounted-epsilon) discounted-shift
           (equiv-reflexive reward-value)
           (equiv-symmetric
            discounted-shift
            (add discounted-right discounted-epsilon)
            distribute-discount))
          target-is-upper
          (equiv-transitive
           target
           (add reward-value (add discounted-right discounted-epsilon))
           ordered-upper associate-target collect-discount)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       unfolded-left
       (action-backup 'S 'A 'states 'transition 'reward 'discount
                      'left-value 'state 'action)
       ordered-upper
       (add
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'right-value 'state 'action)
        discounted-epsilon)
       (equiv-reflexive unfolded-left)
       (equiv-symmetric target ordered-upper target-is-upper)
       reward-bound)))})

(def action-backup-additively-contractive-spec
  (let [left-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'left-value 'state 'action)
        right-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'right-value 'state 'action)
        contracted-epsilon (multiply 'discount 'epsilon)
        left-to-right
        (at-most left-backup (add right-backup contracted-epsilon))
        right-to-left
        (at-most right-backup (add left-backup contracted-epsilon))]
    {:name 'bellman/signed-action-backup-additively-contractive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed]
       ['discount-nonnegative (at-most signed-zero 'discount)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (app 'left-value 'next-state)
                  (add (app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (app 'right-value 'next-state)
                  (add (app 'left-value 'next-state) 'epsilon)))]
       ['state 'S] ['action 'A]
       ['row-nonnegative
        (function/forall
         [['next-state 'S]]
         (at-most signed-zero
                  (app 'transition 'state 'action 'next-state)))]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states (app 'transition 'state 'action))
         signed-one)]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['S type-u] ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S signed)]
       ['reward (function/arrow 'S 'A signed)]
       ['discount signed]
       ['discount-nonnegative (at-most signed-zero 'discount)]
       ['left-value (function/arrow 'S signed)]
       ['right-value (function/arrow 'S signed)]
       ['epsilon signed]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (app 'left-value 'next-state)
                  (add (app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (app 'right-value 'next-state)
                  (add (app 'left-value 'next-state) 'epsilon)))]
       ['state 'S] ['action 'A]
       ['row-nonnegative
        (function/forall
         [['next-state 'S]]
         (at-most signed-zero
                  (app 'transition 'state 'action 'next-state)))]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states (app 'transition 'state 'action))
         signed-one)]]
      (app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (app
        (function/const*
         'bellman/signed-action-backup-additive-upper-bound [U V])
        'S 'A 'states 'transition 'reward 'discount 'discount-nonnegative
        'left-value 'right-value 'epsilon 'left-pointwise
        'state 'action 'row-nonnegative 'row-normalized)
       (app
        (function/const*
         'bellman/signed-action-backup-additive-upper-bound [U V])
        'S 'A 'states 'transition 'reward 'discount 'discount-nonnegative
        'right-value 'left-value 'epsilon 'right-pointwise
        'state 'action 'row-nonnegative 'row-normalized)))}))

(def definition-specs [action-backup-spec])
(def theorem-specs
  [action-backup-unfold-spec
   action-backup-additive-upper-bound-spec
   action-backup-additively-contractive-spec])

(defn- extend-spec-if-missing [env alias producer spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env producer [spec])))

(defn extend-environment [env]
  (-> env
      expectation/extend-environment
      (extend-spec-if-missing
       'signed/add-associative :signed-add-associative
       associative/add-associative-spec)
      (extend-spec-if-missing
       'signed/at-most-respects-equivalence :signed-order-respects
       order-respects/at-most-respects-equivalence-spec)
      (support/extend-with
       :finite-bellman-signed-action-backup
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
