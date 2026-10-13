(ns rainbow.math.finite.bellman-value-iteration-converges
  "Uniform additive convergence bounds for finite Bellman value iteration.

  Bellman optimality and iteration stay opaque. Fixed-point transport uses the
  two-sided contraction theorem; iteration transport uses only propositional
  unfold theorems and equality substitution. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.bellman-backup-contraction :as contraction]
            [rainbow.math.finite.bellman-iterate-monotone :as iterate-monotone]
            [rainbow.math.finite.bellman-optimality :as bellman-optimality]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.archimedean :as archimedean]
            [rainbow.math.rational.nnrat.general-contraction :as general-contraction]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def type-level [:succ [:zero]])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value]
  (function/app (function/const* 'data/succ []) value))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- rows-normalized [state action states transition]
  (function/app (function/const* 'markov/nnrat-rows-normalized [U V])
                state action states transition))

(defn- backup-operator
  [state action states transition reward discount]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount))

(defn- optimality-step
  [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(defn- iterate-value
  [state action actions fallback backup steps initial]
  (function/app (function/const* 'value/nnrat-iterate [U V])
                state action actions fallback backup steps initial))

(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))

(defn- add-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left equivalent-left right equivalent-right
                same-left same-right))

(defn- at-most-respects
  [left equivalent-left right equivalent-right same-left same-right ordered]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence [])
                left equivalent-left right equivalent-right
                same-left same-right ordered))

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
     (source-membership V 'A 'actions (function/app 'fallback 'state)))]
   ['normalized (rows-normalized 'S 'A 'states 'transition)]
   ['fixed-value (function/arrow 'S nnrat)]
   ['fixed-point
    (function/forall
     [['state 'S]]
     (equivalent
      (optimality-step 'S 'A 'actions 'fallback backup 'fixed-value 'state)
      (function/app 'fixed-value 'state)))]])

(def function-additive-upper-transport-spec
  {:name 'value/nnrat-function-additive-upper-transport
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['left (function/arrow 'S nnrat)]
     ['right (function/arrow 'S nnrat)]
     ['same
      (function/equality data-u (function/arrow 'S nnrat) 'left 'right)]
     ['upper (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['state 'S]
     ['ordered
      (at-most (function/app 'left 'state)
               (add (function/app 'upper 'state) 'epsilon))]]
    (at-most (function/app 'right 'state)
             (add (function/app 'upper 'state) 'epsilon)))
   :value
   (function/lam
    [['S type-u]
     ['left (function/arrow 'S nnrat)]
     ['right (function/arrow 'S nnrat)]
     ['same
      (function/equality data-u (function/arrow 'S nnrat) 'left 'right)]
     ['upper (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['state 'S]
     ['ordered
      (at-most (function/app 'left 'state)
               (add (function/app 'upper 'state) 'epsilon))]]
    (function/app
     (function/const* 'equality/substitution [data-u])
     (function/arrow 'S nnrat) 'left 'right 'same
     (function/lam
      [['candidate (function/arrow 'S nnrat)]]
      (at-most (function/app 'candidate 'state)
               (add (function/app 'upper 'state) 'epsilon)))
     'ordered))})

(def function-additive-lower-transport-spec
  {:name 'value/nnrat-function-additive-lower-transport
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['left (function/arrow 'S nnrat)]
     ['right (function/arrow 'S nnrat)]
     ['same
      (function/equality data-u (function/arrow 'S nnrat) 'left 'right)]
     ['lower (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['state 'S]
     ['ordered
      (at-most (function/app 'lower 'state)
               (add (function/app 'left 'state) 'epsilon))]]
    (at-most (function/app 'lower 'state)
             (add (function/app 'right 'state) 'epsilon)))
   :value
   (function/lam
    [['S type-u]
     ['left (function/arrow 'S nnrat)]
     ['right (function/arrow 'S nnrat)]
     ['same
      (function/equality data-u (function/arrow 'S nnrat) 'left 'right)]
     ['lower (function/arrow 'S nnrat)]
     ['epsilon nnrat]
     ['state 'S]
     ['ordered
      (at-most (function/app 'lower 'state)
               (add (function/app 'left 'state) 'epsilon))]]
    (function/app
     (function/const* 'equality/substitution [data-u])
     (function/arrow 'S nnrat) 'left 'right 'same
     (function/lam
      [['candidate (function/arrow 'S nnrat)]]
      (at-most (function/app 'lower 'state)
               (add (function/app 'candidate 'state) 'epsilon)))
     'ordered))})

(def optimality-step-fixed-point-contraction-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        contracted-error (multiply 'discount 'epsilon)
        left-step
        (optimality-step 'S 'A 'actions 'fallback backup 'left-value 'state)
        fixed-step
        (optimality-step 'S 'A 'actions 'fallback backup 'fixed-value 'state)
        fixed-at (function/app 'fixed-value 'state)
        step-left (at-most left-step (add fixed-step contracted-error))
        step-right (at-most fixed-step (add left-step contracted-error))]
    {:name 'value/nnrat-optimality-step-fixed-point-contraction
     :universes ['u 'v]
     :type
     (function/forall
      (concat
       (model-binders backup)
       [['left-value (function/arrow 'S nnrat)]
        ['epsilon nnrat]
        ['left-pointwise
         (function/forall
          [['state 'S]]
          (at-most (function/app 'left-value 'state)
                   (add (function/app 'fixed-value 'state) 'epsilon)))]
        ['right-pointwise
         (function/forall
          [['state 'S]]
          (at-most (function/app 'fixed-value 'state)
                   (add (function/app 'left-value 'state) 'epsilon)))]
        ['state 'S]])
      (proposition/conjunction
       (at-most left-step (add fixed-at contracted-error))
       (at-most fixed-at (add left-step contracted-error))))
     :value
     (function/lam
      (concat
       (model-binders backup)
       [['left-value (function/arrow 'S nnrat)]
        ['epsilon nnrat]
        ['left-pointwise
         (function/forall
          [['state 'S]]
          (at-most (function/app 'left-value 'state)
                   (add (function/app 'fixed-value 'state) 'epsilon)))]
        ['right-pointwise
         (function/forall
          [['state 'S]]
          (at-most (function/app 'fixed-value 'state)
                   (add (function/app 'left-value 'state) 'epsilon)))]
        ['state 'S]])
      (let [contracted
            (function/app
             (function/const*
              'value/nnrat-optimality-step-sup-contraction [U V])
             'S 'A 'states 'actions 'transition 'reward 'discount
             'fallback 'fallback-admissible 'left-value 'fixed-value
             'epsilon 'left-pointwise 'right-pointwise 'normalized 'state)
            fixed-is-step
            (equivalent-symmetric
             fixed-step fixed-at (function/app 'fixed-point 'state))
            fixed-sum-is-step-sum
            (add-respects
             fixed-at fixed-step contracted-error contracted-error
             fixed-is-step (equivalent-reflexive contracted-error))
            result-left
            (at-most-respects
             left-step left-step
             (add fixed-at contracted-error) (add fixed-step contracted-error)
             (equivalent-reflexive left-step) fixed-sum-is-step-sum
             (left-conjunct step-left step-right contracted))
            result-right
            (at-most-respects
             fixed-at fixed-step
             (add left-step contracted-error) (add left-step contracted-error)
             fixed-is-step (equivalent-reflexive (add left-step contracted-error))
             (right-conjunct step-left step-right contracted))]
        (function/app
         (function/const* 'proposition/conjoin [])
         (at-most left-step (add fixed-at contracted-error))
         (at-most fixed-at (add left-step contracted-error))
         result-left result-right)))}))

(def optimality-fixed-point-additive-advance-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        value-function (function/arrow 'S nnrat)
        step-value
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback backup 'candidate 'state))
        close-at
        (fn [value error state]
          (proposition/conjunction
           (at-most (function/app value state)
                    (add (function/app 'fixed-value state) error))
           (at-most (function/app 'fixed-value state)
                    (add (function/app value state) error))))]
    {:name 'value/nnrat-optimality-fixed-point-additive-advance
     :universes ['u 'v]
     :type
     (function/forall
      (model-binders backup)
      (function/forall
       [['candidate value-function]
        ['epsilon nnrat]
        ['close
         (function/forall
          [['state 'S]]
          (close-at 'candidate 'epsilon 'state))]]
       (function/forall
        [['state 'S]]
        (close-at step-value (multiply 'discount 'epsilon) 'state))))
     :value
     (function/lam
      (model-binders backup)
      (function/lam
       [['candidate value-function]
        ['epsilon nnrat]
        ['close
         (function/forall
          [['state 'S]]
          (close-at 'candidate 'epsilon 'state))]]
       (function/lam
        [['state 'S]]
        (function/app
         (function/const*
          'value/nnrat-optimality-step-fixed-point-contraction [U V])
         'S 'A 'states 'actions 'transition 'reward 'discount
         'fallback 'fallback-admissible 'normalized
         'fixed-value 'fixed-point 'candidate 'epsilon
         (function/lam
          [['current 'S]]
          (let [left
                (at-most (function/app 'candidate 'current)
                         (add (function/app 'fixed-value 'current) 'epsilon))
                right
                (at-most (function/app 'fixed-value 'current)
                         (add (function/app 'candidate 'current) 'epsilon))]
            (left-conjunct left right (function/app 'close 'current))))
         (function/lam
          [['current 'S]]
          (let [left
                (at-most (function/app 'candidate 'current)
                         (add (function/app 'fixed-value 'current) 'epsilon))
                right
                (at-most (function/app 'fixed-value 'current)
                         (add (function/app 'candidate 'current) 'epsilon))]
            (right-conjunct left right (function/app 'close 'current))))
         'state))))}))

(def iterate-successor-additive-upper-spec
  (let [value-function (function/arrow 'S nnrat)
        previous
        (iterate-value 'S 'A 'actions 'fallback 'backup 'steps 'initial)
        next
        (iterate-value 'S 'A 'actions 'fallback 'backup
                       (succ 'steps) 'initial)
        successor-result
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback 'backup previous 'state))]
    {:name 'value/nnrat-iterate-successor-additive-upper
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
        ['steps nat]
       ['upper value-function]
        ['epsilon nnrat]
       ['state 'S]
       ['step-bound
        (at-most (function/app successor-result 'state)
                 (add (function/app 'upper 'state) 'epsilon))]]
      (at-most (function/app next 'state)
               (add (function/app 'upper 'state) 'epsilon)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
        ['steps nat]
       ['upper value-function]
        ['epsilon nnrat]
       ['state 'S]
       ['step-bound
        (at-most (function/app successor-result 'state)
                 (add (function/app 'upper 'state) 'epsilon))]]
      (let [successor-unfold
            (function/app
             (function/const* 'value/nnrat-iterate-successor [U V])
             'S 'A 'actions 'fallback 'backup 'steps 'initial)
            result-equals-next
            (function/app
             (function/const* 'equality/symmetric [data-u])
             value-function next successor-result successor-unfold)]
        (function/app
         (function/const* 'value/nnrat-function-additive-upper-transport [U])
         'S successor-result next result-equals-next
         'upper 'epsilon 'state 'step-bound)))}))

(def iterate-successor-additive-lower-spec
  (let [value-function (function/arrow 'S nnrat)
        previous
        (iterate-value 'S 'A 'actions 'fallback 'backup 'steps 'initial)
        next
        (iterate-value 'S 'A 'actions 'fallback 'backup
                       (succ 'steps) 'initial)
        successor-result
        (function/lam
         [['state 'S]]
         (optimality-step 'S 'A 'actions 'fallback 'backup previous 'state))]
    {:name 'value/nnrat-iterate-successor-additive-lower
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['steps nat]
       ['lower value-function]
       ['epsilon nnrat]
       ['state 'S]
       ['step-bound
        (at-most (function/app 'lower 'state)
                 (add (function/app successor-result 'state) 'epsilon))]]
      (at-most (function/app 'lower 'state)
               (add (function/app next 'state) 'epsilon)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['steps nat]
       ['lower value-function]
       ['epsilon nnrat]
       ['state 'S]
       ['step-bound
        (at-most (function/app 'lower 'state)
                 (add (function/app successor-result 'state) 'epsilon))]]
      (let [successor-unfold
            (function/app
             (function/const* 'value/nnrat-iterate-successor [U V])
             'S 'A 'actions 'fallback 'backup 'steps 'initial)
            result-equals-next
            (function/app
             (function/const* 'equality/symmetric [data-u])
             value-function next successor-result successor-unfold)]
        (function/app
         (function/const* 'value/nnrat-function-additive-lower-transport [U])
         'S successor-result next result-equals-next
         'lower 'epsilon 'state 'step-bound)))}))

(def iterate-successor-additively-close-spec
  (let [value-function (function/arrow 'S nnrat)
        previous
        (iterate-value 'S 'A 'actions 'fallback 'backup 'steps 'initial)
        next
        (iterate-value 'S 'A 'actions 'fallback 'backup
                       (succ 'steps) 'initial)
        step-at
        (fn [state]
          (optimality-step 'S 'A 'actions 'fallback 'backup previous state))
        close-at
        (fn [candidate state]
          (proposition/conjunction
           (at-most (function/app candidate state)
                    (add (function/app 'fixed-value state) 'epsilon))
           (at-most (function/app 'fixed-value state)
                    (add (function/app candidate state) 'epsilon))))]
    {:name 'value/nnrat-iterate-successor-additively-close
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['steps nat]
       ['fixed-value value-function]
       ['epsilon nnrat]
       ['step-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (at-most (step-at 'state)
                   (add (function/app 'fixed-value 'state) 'epsilon))
          (at-most (function/app 'fixed-value 'state)
                   (add (step-at 'state) 'epsilon))))]]
      (function/forall [['state 'S]] (close-at next 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['steps nat]
       ['fixed-value value-function]
       ['epsilon nnrat]
       ['step-close
        (function/forall
         [['state 'S]]
         (proposition/conjunction
          (at-most (step-at 'state)
                   (add (function/app 'fixed-value 'state) 'epsilon))
          (at-most (function/app 'fixed-value 'state)
                   (add (step-at 'state) 'epsilon))))]]
      (function/lam
       [['state 'S]]
       (let [step-left
             (at-most (step-at 'state)
                      (add (function/app 'fixed-value 'state) 'epsilon))
             step-right
             (at-most (function/app 'fixed-value 'state)
                      (add (step-at 'state) 'epsilon))
             close (function/app 'step-close 'state)
             result-left
             (function/app
              (function/const* 'value/nnrat-iterate-successor-additive-upper
                               [U V])
              'S 'A 'actions 'fallback 'backup 'initial 'steps
              'fixed-value 'epsilon 'state
              (left-conjunct step-left step-right close))
             result-right
             (function/app
              (function/const* 'value/nnrat-iterate-successor-additive-lower
                               [U V])
              'S 'A 'actions 'fallback 'backup 'initial 'steps
              'fixed-value 'epsilon 'state
              (right-conjunct step-left step-right close))]
         (function/app
          (function/const* 'proposition/conjoin [])
          (at-most (function/app next 'state)
                   (add (function/app 'fixed-value 'state) 'epsilon))
          (at-most (function/app 'fixed-value 'state)
                   (add (function/app next 'state) 'epsilon))
          result-left result-right))))}))

(def iterate-zero-additively-close-spec
  (let [value-function (function/arrow 'S nnrat)
        zero (function/const* 'data/zero [])
        iterated
        (iterate-value 'S 'A 'actions 'fallback 'backup zero 'initial)
        close-at
        (fn [candidate state]
          (proposition/conjunction
           (at-most (function/app candidate state)
                    (add (function/app 'fixed-value state) 'epsilon))
           (at-most (function/app 'fixed-value state)
                    (add (function/app candidate state) 'epsilon))))]
    {:name 'value/nnrat-iterate-zero-additively-close
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['fixed-value value-function]
       ['epsilon nnrat]
       ['initial-close
        (function/forall [['state 'S]] (close-at 'initial 'state))]]
      (function/forall [['state 'S]] (close-at iterated 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['initial value-function]
       ['fixed-value value-function]
       ['epsilon nnrat]
       ['initial-close
        (function/forall [['state 'S]] (close-at 'initial 'state))]]
      (function/lam
       [['state 'S]]
       (let [initial-at (function/app 'initial 'state)
             iterated-at (function/app iterated 'state)
             fixed-at (function/app 'fixed-value 'state)
             zero-unfold
             (function/app
              (function/const* 'value/nnrat-iterate-zero [U V])
              'S 'A 'actions 'fallback 'backup 'initial 'state)
             initial-equals-iterated
             (function/app
              (function/const* 'equality/symmetric [type-level])
              nnrat iterated-at initial-at zero-unfold)
             initial-left
               (at-most (function/app 'initial 'state)
                        (add (function/app 'fixed-value 'state) 'epsilon))
             initial-right
             (at-most (function/app 'fixed-value 'state)
                      (add (function/app 'initial 'state) 'epsilon))
             close (function/app 'initial-close 'state)
             result-left
             (function/app
              (function/const* 'equality/substitution [type-level])
              nnrat initial-at iterated-at initial-equals-iterated
              (function/lam
               [['candidate nnrat]]
               (at-most 'candidate (add fixed-at 'epsilon)))
              (left-conjunct initial-left initial-right close))
             result-right
             (function/app
              (function/const* 'equality/substitution [type-level])
              nnrat initial-at iterated-at initial-equals-iterated
              (function/lam
               [['candidate nnrat]]
               (at-most fixed-at (add 'candidate 'epsilon)))
              (right-conjunct initial-left initial-right close))]
         (function/app
          (function/const* 'proposition/conjoin [])
          (at-most iterated-at (add fixed-at 'epsilon))
          (at-most fixed-at (add iterated-at 'epsilon))
          result-left result-right))))}))

(def vi-error-radius-spec
  {:name 'value/nnrat-vi-error-radius
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nat nnrat)
   :value
   (function/lam
    [['discount nnrat] ['initial-error nnrat] ['steps nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     'initial-error
     (function/lam
      [['ignored nat] ['previous nnrat]]
      (multiply 'discount 'previous))
     'steps))})

(def iterate-fixed-point-additive-radius-spec
  (let [value-function (function/arrow 'S nnrat)
        radius
        (fn [steps]
          (function/app (function/const* 'value/nnrat-vi-error-radius [])
                        'discount 'initial-error steps))
        iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback 'backup steps 'initial))
        step-value
        (fn [candidate]
          (function/lam
           [['state 'S]]
           (optimality-step 'S 'A 'actions 'fallback 'backup
                            candidate 'state)))
        close-at
        (fn [candidate error state]
          (proposition/conjunction
           (at-most (function/app candidate state)
                    (add (function/app 'fixed-value state) error))
           (at-most (function/app 'fixed-value state)
                    (add (function/app candidate state) error))))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (close-at (iterated 'steps) (radius 'steps) 'state)))]
    {:name 'value/nnrat-iterate-fixed-point-additive-radius
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['discount nnrat]
       ['fixed-value value-function]
       ['initial value-function]
       ['initial-error nnrat]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]
       ['advance
        (function/forall
         [['candidate value-function]
          ['epsilon nnrat]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'candidate 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (step-value 'candidate)
                    (multiply 'discount 'epsilon) 'state)))]]
      (function/forall
       [['steps nat] ['state 'S]]
       (close-at (iterated 'steps) (radius 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['discount nnrat]
       ['fixed-value value-function]
       ['initial value-function]
       ['initial-error nnrat]
       ['initial-close
        (function/forall
         [['state 'S]]
         (close-at 'initial 'initial-error 'state))]
       ['advance
        (function/forall
         [['candidate value-function]
          ['epsilon nnrat]
          ['close
           (function/forall
            [['state 'S]]
            (close-at 'candidate 'epsilon 'state))]]
         (function/forall
          [['state 'S]]
          (close-at (step-value 'candidate)
                    (multiply 'discount 'epsilon) 'state)))]]
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'data/Nat.rec [[:zero]])
        motive
        (function/app
         (function/const* 'value/nnrat-iterate-zero-additively-close [U V])
         'S 'A 'actions 'fallback 'backup 'initial
         'fixed-value 'initial-error 'initial-close)
        (function/lam
         [['previous-steps nat]
          ['induction-hypothesis (function/app motive 'previous-steps)]]
         (let [previous (iterated 'previous-steps)
               previous-radius (radius 'previous-steps)
               next-error (multiply 'discount previous-radius)
               step-close
               (function/app 'advance previous previous-radius
                             'induction-hypothesis)]
           (function/app
            (function/const* 'value/nnrat-iterate-successor-additively-close
                             [U V])
            'S 'A 'actions 'fallback 'backup 'initial 'previous-steps
            'fixed-value next-error step-close)))
        'steps)))}))

(def vi-error-radius-rate-null-spec
  (let [zero (function/const* 'data/zero [])
        gamma
        (function/app
         (function/const* 'nnrat/make [])
         (succ 'ap)
         (function/app (function/const* 'algebra/nat-add [])
                       'ap (succ 'gp)))
        radius
        (function/app (function/const* 'value/nnrat-vi-error-radius [])
                      gamma 'initial-error)
        harmonic-zero
        (function/app (function/const* 'nnrat/general-harmonic [])
                      'ap 'gp zero)
        modulus
        (function/lam
         [['k nat]]
         (function/app (function/const* 'nat/multiply [])
                       (succ 'ap) 'k))]
    {:name 'analysis/nnrat-vi-error-radius-rate-null
     :universes []
     :type
     (function/forall
      [['ap nat]
       ['gp nat]
       ['initial-error nnrat]
       ['initial-bound
        (at-most (function/app radius zero) harmonic-zero)]]
      (function/app (function/const* 'analysis/rate-null [])
                    radius modulus))
     :value
     (function/lam
      [['ap nat]
       ['gp nat]
       ['initial-error nnrat]
       ['initial-bound
        (at-most (function/app radius zero) harmonic-zero)]]
      (function/app
       (function/const* 'analysis/general-contraction-converges [])
       'ap 'gp radius 'initial-bound
       (function/lam
        [['steps nat]]
        (function/app
         (function/const* 'nnrat/at-most-reflexive [])
         (multiply gamma (function/app radius 'steps))))))}))

(def optimality-iterate-fixed-point-converges-spec
  (let [zero (function/const* 'data/zero [])
        gamma
        (function/app
         (function/const* 'nnrat/make [])
         (succ 'ap)
         (function/app (function/const* 'algebra/nat-add [])
                       'ap (succ 'gp)))
        backup
        (backup-operator 'S 'A 'states 'transition 'reward gamma)
        value-function (function/arrow 'S nnrat)
        radius
        (function/app (function/const* 'value/nnrat-vi-error-radius [])
                      gamma 'initial-error)
        iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback backup steps 'initial))
        close-at
        (fn [steps state]
          (proposition/conjunction
           (at-most (function/app (iterated steps) state)
                    (add (function/app 'fixed-value state)
                         (function/app radius steps)))
           (at-most (function/app 'fixed-value state)
                    (add (function/app (iterated steps) state)
                         (function/app radius steps)))))
        harmonic-zero
        (function/app (function/const* 'nnrat/general-harmonic [])
                      'ap 'gp zero)
        modulus
        (function/lam
         [['k nat]]
         (function/app (function/const* 'nat/multiply [])
                       (succ 'ap) 'k))
        radius-null
        (function/app (function/const* 'analysis/rate-null [])
                      radius modulus)
        iterate-bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (close-at 'steps 'state))
        binders
        [['ap nat]
         ['gp nat]
         ['S type-u]
         ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['actions (exact-finset-of V 'A)]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A nnrat)]
         ['fallback (function/arrow 'S 'A)]
         ['fallback-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions
                              (function/app 'fallback 'state)))]
         ['normalized (rows-normalized 'S 'A 'states 'transition)]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (equivalent
            (optimality-step 'S 'A 'actions 'fallback backup
                             'fixed-value 'state)
            (function/app 'fixed-value 'state)))]
         ['initial value-function]
         ['initial-error nnrat]
         ['initial-bound
          (at-most (function/app radius zero) harmonic-zero)]
         ['initial-close
          (function/forall
           [['state 'S]]
           (proposition/conjunction
            (at-most (function/app 'initial 'state)
                     (add (function/app 'fixed-value 'state) 'initial-error))
            (at-most (function/app 'fixed-value 'state)
                     (add (function/app 'initial 'state) 'initial-error))))]]]
    {:name 'value/nnrat-optimality-iterate-fixed-point-converges
     :universes ['u 'v]
     :type
     (function/forall binders
                      (proposition/conjunction radius-null iterate-bounds))
     :value
     (function/lam
      binders
      (let [null-proof
            (function/app
             (function/const* 'analysis/nnrat-vi-error-radius-rate-null [])
             'ap 'gp 'initial-error 'initial-bound)
            advance
            (function/app
             (function/const*
              'value/nnrat-optimality-fixed-point-additive-advance [U V])
             'S 'A 'states 'actions 'transition 'reward gamma
             'fallback 'fallback-admissible 'normalized
             'fixed-value 'fixed-point)
            bounds-proof
            (function/app
             (function/const*
              'value/nnrat-iterate-fixed-point-additive-radius [U V])
             'S 'A 'actions 'fallback backup gamma
             'fixed-value 'initial 'initial-error 'initial-close advance)]
        (function/app
         (function/const* 'proposition/conjoin [])
         radius-null iterate-bounds null-proof bounds-proof)))}))

(def at-most-of-rate-null-upper-bounds-spec
  (let [one (succ (function/const* 'data/zero []))
        reciprocal
        (fn [k]
          (function/app (function/const* 'nnrat/make []) one k))]
    {:name 'analysis/nnrat-at-most-of-rate-null-upper-bounds
     :universes []
     :type
     (function/forall
      [['error (function/arrow nat nnrat)]
       ['modulus (function/arrow nat nat)]
       ['x nnrat]
       ['y nnrat]
       ['null
        (function/app (function/const* 'analysis/rate-null [])
                      'error 'modulus)]
       ['bounded
        (function/forall
         [['steps nat]]
         (at-most 'x (add 'y (function/app 'error 'steps))))]]
      (at-most 'x 'y))
     :value
     (function/lam
      [['error (function/arrow nat nnrat)]
       ['modulus (function/arrow nat nat)]
       ['x nnrat]
       ['y nnrat]
       ['null
        (function/app (function/const* 'analysis/rate-null [])
                      'error 'modulus)]
       ['bounded
        (function/forall
         [['steps nat]]
         (at-most 'x (add 'y (function/app 'error 'steps))))]]
      (function/app
       (function/const* 'nnrat/at-most-of-all-plus-reciprocal [])
       'x 'y
       (function/lam
        [['k nat]]
        (let [steps (function/app 'modulus 'k)
              error-at (function/app 'error steps)
              harmonic-at (reciprocal 'k)
              error-small
              (function/app
               'null 'k steps
               (function/app (function/const* 'nat/at-most-reflexive [])
                             steps))
              add-small
              (function/app
               (function/const* 'nnrat/add-left-monotone [])
               'y error-at harmonic-at error-small)]
          (function/app
           (function/const* 'nnrat/at-most-transitive [])
           'x (add 'y error-at) (add 'y harmonic-at)
           (function/app 'bounded steps) add-small)))))}))

(def bellman-fixed-point-dominates-post-fixed-value-spec
  (let [zero (function/const* 'data/zero [])
        gamma
        (function/app
         (function/const* 'nnrat/make [])
         (succ 'ap)
         (function/app (function/const* 'algebra/nat-add [])
                       'ap (succ 'gp)))
        backup
        (backup-operator 'S 'A 'states 'transition 'reward gamma)
        value-function (function/arrow 'S nnrat)
        radius
        (function/app (function/const* 'value/nnrat-vi-error-radius [])
                      gamma 'initial-error)
        iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback backup
                         steps 'post-fixed-value))
        harmonic-zero
        (function/app (function/const* 'nnrat/general-harmonic [])
                      'ap 'gp zero)
        modulus
        (function/lam
         [['k nat]]
         (function/app (function/const* 'nat/multiply [])
                       (succ 'ap) 'k))
        radius-null
        (function/app (function/const* 'analysis/rate-null [])
                      radius modulus)
        iterate-close-at
        (fn [steps state]
          (proposition/conjunction
           (at-most (function/app (iterated steps) state)
                    (add (function/app 'fixed-value state)
                         (function/app radius steps)))
           (at-most (function/app 'fixed-value state)
                    (add (function/app (iterated steps) state)
                         (function/app radius steps)))))
        iterate-bounds
        (function/forall
         [['steps nat] ['state 'S]]
         (iterate-close-at 'steps 'state))
        binders
        [['ap nat]
         ['gp nat]
         ['S type-u]
         ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['actions (exact-finset-of V 'A)]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A nnrat)]
         ['fallback (function/arrow 'S 'A)]
         ['fallback-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions
                              (function/app 'fallback 'state)))]
         ['normalized (rows-normalized 'S 'A 'states 'transition)]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (equivalent
            (optimality-step 'S 'A 'actions 'fallback backup
                             'fixed-value 'state)
            (function/app 'fixed-value 'state)))]
         ['post-fixed-value value-function]
         ['below-step
          (function/forall
           [['state 'S]]
           (at-most
            (function/app 'post-fixed-value 'state)
            (optimality-step 'S 'A 'actions 'fallback backup
                             'post-fixed-value 'state)))]
         ['initial-error nnrat]
         ['initial-bound
          (at-most (function/app radius zero) harmonic-zero)]
         ['initial-close
          (function/forall
           [['state 'S]]
           (proposition/conjunction
            (at-most (function/app 'post-fixed-value 'state)
                     (add (function/app 'fixed-value 'state) 'initial-error))
            (at-most (function/app 'fixed-value 'state)
                     (add (function/app 'post-fixed-value 'state)
                          'initial-error))))]]]
    {:name 'value/nnrat-bellman-fixed-point-dominates-post-fixed-value
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (at-most (function/app 'post-fixed-value 'state)
                (function/app 'fixed-value 'state))))
     :value
     (function/lam
      binders
      (let [converged
            (function/app
             (function/const*
              'value/nnrat-optimality-iterate-fixed-point-converges [U V])
             'ap 'gp 'S 'A 'states 'actions 'transition 'reward
             'fallback 'fallback-admissible 'normalized
             'fixed-value 'fixed-point 'post-fixed-value
             'initial-error 'initial-bound 'initial-close)
            null-proof
            (left-conjunct radius-null iterate-bounds converged)
            bounds-proof
            (right-conjunct radius-null iterate-bounds converged)]
        (function/lam
         [['state 'S]]
         (function/app
          (function/const*
           'analysis/nnrat-at-most-of-rate-null-upper-bounds [])
          radius modulus
          (function/app 'post-fixed-value 'state)
          (function/app 'fixed-value 'state)
          null-proof
          (function/lam
           [['steps nat]]
           (let [iterate-at (function/app (iterated 'steps) 'state)
                 fixed-at (function/app 'fixed-value 'state)
                 error-at (function/app radius 'steps)
                 below-iterate
                 (function/app
                  (function/const*
                   'value/nnrat-value-below-optimality-iterate [U V])
                  'S 'A 'states 'actions 'transition 'reward gamma
                  'fallback 'fallback-admissible
                  'post-fixed-value 'below-step 'steps 'state)
                 iterate-upper
                 (left-conjunct
                  (at-most iterate-at (add fixed-at error-at))
                  (at-most fixed-at (add iterate-at error-at))
                  (function/app bounds-proof 'steps 'state))]
             (function/app
              (function/const* 'nnrat/at-most-transitive [])
              (function/app 'post-fixed-value 'state)
              iterate-at (add fixed-at error-at)
              below-iterate iterate-upper)))))))}))

(def policy-fixed-point-below-optimality-step-spec
  (let [value-function (function/arrow 'S nnrat)
        policy-backup
        (function/app 'backup 'value 'state (function/app 'policy 'state))
        optimum
        (optimality-step 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/nnrat-policy-fixed-point-below-optimality-step
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['value value-function]
       ['policy (function/arrow 'S 'A)]
       ['policy-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions
                            (function/app 'policy 'state)))]
       ['policy-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'value 'state)
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))))]
       ['state 'S]]
      (at-most (function/app 'value 'state) optimum))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow value-function 'S 'A nnrat)]
       ['value value-function]
       ['policy (function/arrow 'S 'A)]
       ['policy-admissible
        (function/forall
         [['state 'S]]
         (source-membership V 'A 'actions
                            (function/app 'policy 'state)))]
       ['policy-fixed-point
        (function/forall
         [['state 'S]]
         (equivalent
          (function/app 'value 'state)
          (function/app 'backup 'value 'state
                        (function/app 'policy 'state))))]
       ['state 'S]]
      (function/app
       (function/const* 'nnrat/at-most-transitive [])
       (function/app 'value 'state) policy-backup optimum
       (function/app
        (function/const* 'nnrat/equivalent-to-at-most [])
        (function/app 'value 'state) policy-backup
        (function/app 'policy-fixed-point 'state))
       (function/app
        (function/const* 'value/nnrat-optimality-step-dominates-policy [U V])
        'S 'A 'actions 'fallback 'backup 'value
        'policy 'policy-admissible 'state)))}))

(def policy-value-below-bellman-fixed-point-spec
  (let [zero (function/const* 'data/zero [])
        gamma
        (function/app
         (function/const* 'nnrat/make [])
         (succ 'ap)
         (function/app (function/const* 'algebra/nat-add [])
                       'ap (succ 'gp)))
        backup
        (backup-operator 'S 'A 'states 'transition 'reward gamma)
        value-function (function/arrow 'S nnrat)
        radius
        (function/app (function/const* 'value/nnrat-vi-error-radius [])
                      gamma 'initial-error)
        harmonic-zero
        (function/app (function/const* 'nnrat/general-harmonic [])
                      'ap 'gp zero)
        binders
        [['ap nat]
         ['gp nat]
         ['S type-u]
         ['A type-v]
         ['states (exact-finset-of U 'S)]
         ['actions (exact-finset-of V 'A)]
         ['transition (function/arrow 'S 'A 'S nnrat)]
         ['reward (function/arrow 'S 'A nnrat)]
         ['fallback (function/arrow 'S 'A)]
         ['fallback-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions
                              (function/app 'fallback 'state)))]
         ['normalized (rows-normalized 'S 'A 'states 'transition)]
         ['fixed-value value-function]
         ['fixed-point
          (function/forall
           [['state 'S]]
           (equivalent
            (optimality-step 'S 'A 'actions 'fallback backup
                             'fixed-value 'state)
            (function/app 'fixed-value 'state)))]
         ['policy (function/arrow 'S 'A)]
         ['policy-admissible
          (function/forall
           [['state 'S]]
           (source-membership V 'A 'actions
                              (function/app 'policy 'state)))]
         ['policy-value value-function]
         ['policy-fixed-point
          (function/forall
           [['state 'S]]
           (equivalent
            (function/app 'policy-value 'state)
            (function/app backup 'policy-value 'state
                          (function/app 'policy 'state))))]
         ['initial-error nnrat]
         ['initial-bound
          (at-most (function/app radius zero) harmonic-zero)]
         ['initial-close
          (function/forall
           [['state 'S]]
           (proposition/conjunction
            (at-most (function/app 'policy-value 'state)
                     (add (function/app 'fixed-value 'state) 'initial-error))
            (at-most (function/app 'fixed-value 'state)
                     (add (function/app 'policy-value 'state)
                          'initial-error))))]]]
    {:name 'value/nnrat-policy-value-below-bellman-fixed-point
     :universes ['u 'v]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'S]]
       (at-most (function/app 'policy-value 'state)
                (function/app 'fixed-value 'state))))
     :value
     (function/lam
      binders
      (function/app
       (function/const*
        'value/nnrat-bellman-fixed-point-dominates-post-fixed-value [U V])
       'ap 'gp 'S 'A 'states 'actions 'transition 'reward
       'fallback 'fallback-admissible 'normalized
       'fixed-value 'fixed-point 'policy-value
       (function/lam
        [['state 'S]]
        (function/app
         (function/const*
          'value/nnrat-policy-fixed-point-below-optimality-step [U V])
         'S 'A 'actions 'fallback backup 'policy-value
         'policy 'policy-admissible 'policy-fixed-point 'state))
       'initial-error 'initial-bound 'initial-close))}))

(def definition-specs [vi-error-radius-spec])
(def theorem-specs
  [function-additive-upper-transport-spec
   function-additive-lower-transport-spec
   optimality-step-fixed-point-contraction-spec
   optimality-fixed-point-additive-advance-spec
   iterate-successor-additive-upper-spec
   iterate-successor-additive-lower-spec
   iterate-successor-additively-close-spec
   iterate-zero-additively-close-spec
   iterate-fixed-point-additive-radius-spec
   vi-error-radius-rate-null-spec
   optimality-iterate-fixed-point-converges-spec
   at-most-of-rate-null-upper-bounds-spec
   bellman-fixed-point-dominates-post-fixed-value-spec
   policy-fixed-point-below-optimality-step-spec
   policy-value-below-bellman-fixed-point-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.archimedean rainbow.math.finite.bellman-optimality rainbow.math.finite.bellman-backup-contraction rainbow.math.finite.bellman-iterate-monotone rainbow.math.rational.nnrat.general-contraction])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-bellman-value-iteration-converges (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman-value-iteration-converges))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
