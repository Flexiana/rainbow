(ns rainbow.math.rational.nnrat.diagonal-spike
  "Canonical exact-rational diagonal spikes over duplicate-free finite carriers.

  A Boolean equality decision is supplied together with proofs that `true`
  reflects and is complete for propositional equality.  The executable spike
  puts a row mass at its selected state and zero elsewhere.  Duplicate freedom
  and membership of the selected state imply that its finite sum is exactly the
  supplied mass.  A certified exhaustive carrier packages equality correctness
  with coverage of every ambient state, so downstream kernels need one coherent
  finite-state certificate rather than two unrelated premises.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.list-sum :as list-sum]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-u]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [data-u]) element))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- duplicate-free [element source]
  (app (function/const* 'finset-data/duplicate-free [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- no-duplicates [element items]
  (app (function/const* 'list/no-duplicates [U]) element items))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- eq-state [element left right]
  (function/equality data-u element left right))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- decision-true [decision left right]
  (eq-bool (app decision left right) true-value))
(defn- equality-soundness [element decision]
  (function/forall
   [['left element] ['right element]
    ['accepted (decision-true decision 'left 'right)]]
   (eq-state element 'left 'right)))
(defn- equality-completeness [element decision]
  (function/forall
   [['left element] ['right element]
    ['same (eq-state element 'left 'right)]]
   (decision-true decision 'left 'right)))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [U])
       element decision))
(defn- carrier-covered [element states]
  (function/forall
   [['state element]]
   (membership element (enumeration element states) 'state)))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- selected-at [when-false when-true decision]
  (app (function/const* 'data/Bool.rec [type-level])
       (function/lam [['ignored bool]] nnrat)
       when-false when-true decision))
(defn- diagonal-spike [element decision mass selected candidate]
  (app (function/const* 'finite/nnrat-diagonal-spike [U])
       element decision mass selected candidate))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- add-respects [left left-prime right right-prime same-left same-right]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime same-left same-right))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- left-disjunct [left right evidence]
  (app (function/const* 'proposition/left-disjunct [])
       left right evidence))
(defn- right-disjunct [left right evidence]
  (app (function/const* 'proposition/right-disjunct [])
       left right evidence))
(defn- use-disjunction [left right result evidence on-left on-right]
  (app (function/const* 'proposition/use-disjunction [])
       left right result evidence on-left on-right))
(defn- explode [result contradiction]
  (app (function/const* 'proposition/explode []) result contradiction))
(defn- bool-reflexive [value]
  (app (function/const* 'equality/reflexive [type-level]) bool value))
(defn- bool-symmetric [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       bool left right same))
(defn- bool-transitive [left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       bool left middle right first second))
(defn- substitute-state [element left right same predicate at-left]
  (app (function/const* 'equality/substitution [data-u])
       element left right same predicate at-left))

(defn- false-not-true [same]
  (let [predicate
        (function/lam
         [['value bool]]
         (app (function/const* 'data/Bool.rec [type-level])
              (function/lam [['ignored bool]] 'Prop)
              (proposition/truth) (proposition/falsity) 'value))]
    (app same predicate
         (function/const* 'proposition/trivial []))))

(defn- bool-case [decision goal-of false-branch true-branch]
  (let [motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (eq-bool decision 'choice)
          (goal-of 'choice)))]
    (app
     (app (function/const* 'data/Bool.rec [zero-level])
          motive
          (function/lam
           [['decision-is-false (eq-bool decision false-value)]]
           (false-branch 'decision-is-false))
          (function/lam
           [['decision-is-true (eq-bool decision true-value)]]
           (true-branch 'decision-is-true))
          decision)
     (bool-reflexive decision))))

(def certified-equality-decision-spec
  {:name 'finite/certified-equality-decision
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]]
    (proposition/conjunction
     (equality-soundness 'S 'decision)
     (equality-completeness 'S 'decision)))})

(def certified-exhaustive-carrier-spec
  {:name 'finite/certified-exhaustive-carrier
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]]
    (proposition/conjunction
     (certified-equality 'S 'decision)
     (carrier-covered 'S 'states)))})

(def certified-equality-of-exhaustive-carrier-spec
  {:name 'finite/certified-equality-of-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]]
    (certified-equality 'S 'decision))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]]
    (left-conjunct
     (certified-equality 'S 'decision)
     (carrier-covered 'S 'states)
     'exhaustive))})

(def coverage-of-exhaustive-carrier-spec
  {:name 'finite/coverage-of-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]]
    (carrier-covered 'S 'states))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]]
    (right-conjunct
     (certified-equality 'S 'decision)
     (carrier-covered 'S 'states)
     'exhaustive))})

(def diagonal-spike-spec
  {:name 'finite/nnrat-diagonal-spike
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['selected 'S] ['candidate 'S]]
    (selected-at nnrat-zero (app 'mass 'selected)
                 (app 'decision 'selected 'candidate)))})

(def diagonal-spike-zero-of-different-spec
  {:name 'finite/nnrat-diagonal-spike-zero-of-different
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]
     ['different
      (proposition/negation
       (eq-state 'S 'selected 'candidate))]]
    (req (diagonal-spike 'S 'decision 'mass 'selected 'candidate)
         nnrat-zero))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]
     ['different
      (proposition/negation
       (eq-state 'S 'selected 'candidate))]]
    (let [choice (app 'decision 'selected 'candidate)
          soundness
          (left-conjunct
           (equality-soundness 'S 'decision)
           (equality-completeness 'S 'decision)
           'certified)]
      (bool-case
       choice
       (fn [flag]
         (req (selected-at nnrat-zero (app 'mass 'selected) flag)
              nnrat-zero))
       (fn [_] (equivalent-reflexive nnrat-zero))
       (fn [accepted]
         (explode
          (req (app 'mass 'selected) nnrat-zero)
          (app 'different
               (app soundness 'selected 'candidate accepted)))))))})

(def equality-decidable-of-certified-decision-spec
  {:name 'finite/equality-decidable-of-certified-decision
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality 'S 'decision)]
     ['left 'S] ['right 'S]]
    (proposition/disjunction
     (eq-state 'S 'left 'right)
     (proposition/negation (eq-state 'S 'left 'right))))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality 'S 'decision)]
     ['left 'S] ['right 'S]]
    (let [choice (app 'decision 'left 'right)
          same (eq-state 'S 'left 'right)
          different (proposition/negation same)
          result (proposition/disjunction same different)
          soundness
          (left-conjunct
           (equality-soundness 'S 'decision)
           (equality-completeness 'S 'decision) 'certified)
          completeness
          (right-conjunct
           (equality-soundness 'S 'decision)
           (equality-completeness 'S 'decision) 'certified)]
      (bool-case
       choice
       (fn [_] result)
       (fn [rejected]
         (right-disjunct
          same different
          (function/lam
           [['same-state same]]
           (false-not-true
            (bool-transitive
             false-value choice true-value
             (bool-symmetric choice false-value rejected)
             (app completeness 'left 'right 'same-state))))))
       (fn [accepted]
         (left-disjunct
          same different
          (app soundness 'left 'right accepted))))))})

(def diagonal-spike-mass-of-equal-spec
  {:name 'finite/nnrat-diagonal-spike-mass-of-equal
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]
     ['same (eq-state 'S 'selected 'candidate)]]
    (req (diagonal-spike 'S 'decision 'mass 'selected 'candidate)
         (app 'mass 'selected)))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]
     ['same (eq-state 'S 'selected 'candidate)]]
    (let [choice (app 'decision 'selected 'candidate)
          completeness
          (right-conjunct
           (equality-soundness 'S 'decision)
           (equality-completeness 'S 'decision)
           'certified)
          accepted (app completeness 'selected 'candidate 'same)]
      (bool-case
       choice
       (fn [flag]
         (req (selected-at nnrat-zero (app 'mass 'selected) flag)
              (app 'mass 'selected)))
       (fn [rejected]
         (explode
          (req nnrat-zero (app 'mass 'selected))
          (false-not-true
           (bool-transitive
            false-value choice true-value
            (bool-symmetric choice false-value rejected)
            accepted))))
       (fn [_] (equivalent-reflexive (app 'mass 'selected))))))})

(def diagonal-unit-spike-multiply-spec
  {:name 'finite/nnrat-diagonal-unit-spike-multiply
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]]
    (req
     (rmul
      (diagonal-spike
       'S 'decision
       (function/lam [['ignored 'S]] nnrat-one)
       'selected 'candidate)
      (app 'mass 'candidate))
     (diagonal-spike
      'S 'decision 'mass 'selected 'candidate)))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S] ['candidate 'S]]
    (let [choice (app 'decision 'selected 'candidate)
          soundness
          (left-conjunct
           (equality-soundness 'S 'decision)
           (equality-completeness 'S 'decision)
           'certified)]
      (bool-case
       choice
       (fn [flag]
         (req
          (rmul
           (selected-at nnrat-zero nnrat-one flag)
           (app 'mass 'candidate))
          (selected-at nnrat-zero (app 'mass 'selected) flag)))
       (fn [_]
         (app (function/const* 'nnrat/multiply-zero-left [])
              (app 'mass 'candidate)))
       (fn [accepted]
         (let [same (app soundness 'selected 'candidate accepted)
               predicate
               (function/lam
                [['state 'S]]
                (req
                 (rmul nnrat-one (app 'mass 'state))
                 (app 'mass 'selected)))]
           (substitute-state
            'S 'selected 'candidate same predicate
            (app (function/const* 'nnrat/multiply-one-left [])
                 (app 'mass 'selected))))))))})

(def map-sum-diagonal-spike-zero-of-not-member-spec
  (let [motive
        (function/lam
         [['items (list-of 'S)]]
         (function/forall
          [['selected 'S]
           ['not-member
            (proposition/negation
             (membership 'S 'items 'selected))]]
          (req
           (map-sum
            'S
            (function/lam
             [['candidate 'S]]
             (diagonal-spike
              'S 'decision 'mass 'selected 'candidate))
            'items)
           nnrat-zero)))]
    {:name 'finite/nnrat-map-sum-diagonal-spike-zero-of-not-member
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['decision (function/arrow 'S 'S bool)]
       ['mass (function/arrow 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['items (list-of 'S)]
       ['selected 'S]
       ['not-member
        (proposition/negation
         (membership 'S 'items 'selected))]]
      (req
       (map-sum
        'S
        (function/lam
         [['candidate 'S]]
         (diagonal-spike 'S 'decision 'mass 'selected 'candidate))
        'items)
       nnrat-zero))
     :value
     (function/lam
      [['S type-u]
       ['decision (function/arrow 'S 'S bool)]
       ['mass (function/arrow 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['items (list-of 'S)]
       ['selected 'S]
       ['not-member
        (proposition/negation
         (membership 'S 'items 'selected))]]
      (app
       (function/const* 'data/List.rec [data-u zero-level])
       'S motive
       (function/lam
        [['selected 'S]
         ['ignored
          (proposition/negation
           (membership 'S (nil-list 'S) 'selected))]]
        (equivalent-reflexive nnrat-zero))
       (function/lam
        [['head 'S] ['tail (list-of 'S)]
         ['induction-hypothesis (app motive 'tail)]
         ['selected 'S]
         ['not-member
          (proposition/negation
           (membership
            'S
            (app (function/const* 'data/cons [data-u])
                 'S 'head 'tail)
            'selected))]]
        (let [head-same (eq-state 'S 'selected 'head)
              tail-member (membership 'S 'tail 'selected)
              head-different
              (function/lam
               [['same head-same]]
               (app 'not-member
                    (left-disjunct head-same tail-member 'same)))
              tail-not-member
              (function/lam
               [['member tail-member]]
               (app 'not-member
                    (right-disjunct head-same tail-member 'member)))
              head-zero
              (app
               (function/const*
                'finite/nnrat-diagonal-spike-zero-of-different [U])
               'S 'decision 'mass 'certified
               'selected 'head head-different)
              tail-zero
              (app 'induction-hypothesis 'selected tail-not-member)
              sum
              (radd
               (diagonal-spike 'S 'decision 'mass 'selected 'head)
               (map-sum
                'S
                (function/lam
                 [['candidate 'S]]
                 (diagonal-spike
                  'S 'decision 'mass 'selected 'candidate))
                'tail))]
          (equivalent-transitive
           sum (radd nnrat-zero nnrat-zero) nnrat-zero
           (add-respects
            (diagonal-spike 'S 'decision 'mass 'selected 'head)
            nnrat-zero
            (map-sum
             'S
             (function/lam
              [['candidate 'S]]
              (diagonal-spike
               'S 'decision 'mass 'selected 'candidate))
             'tail)
            nnrat-zero head-zero tail-zero)
           (equivalent-reflexive nnrat-zero))))
       'items 'selected 'not-member))}))

(def map-sum-diagonal-spike-of-member-no-duplicates-spec
  (let [motive
        (function/lam
         [['items (list-of 'S)]]
         (function/forall
          [['selected 'S]
           ['distinct (no-duplicates 'S 'items)]
           ['member (membership 'S 'items 'selected)]]
          (req
           (map-sum
            'S
            (function/lam
             [['candidate 'S]]
             (diagonal-spike
              'S 'decision 'mass 'selected 'candidate))
            'items)
           (app 'mass 'selected))))]
    {:name 'finite/nnrat-map-sum-diagonal-spike-of-member-no-duplicates
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['decision (function/arrow 'S 'S bool)]
       ['mass (function/arrow 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['items (list-of 'S)]
       ['selected 'S]
       ['distinct (no-duplicates 'S 'items)]
       ['member (membership 'S 'items 'selected)]]
      (req
       (map-sum
        'S
        (function/lam
         [['candidate 'S]]
         (diagonal-spike 'S 'decision 'mass 'selected 'candidate))
        'items)
       (app 'mass 'selected)))
     :value
     (function/lam
      [['S type-u]
       ['decision (function/arrow 'S 'S bool)]
       ['mass (function/arrow 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['items (list-of 'S)]
       ['selected 'S]
       ['distinct (no-duplicates 'S 'items)]
       ['member (membership 'S 'items 'selected)]]
      (app
       (function/const* 'data/List.rec [data-u zero-level])
       'S motive
       (function/lam
        [['selected 'S]
         ['ignored-distinct (no-duplicates 'S (nil-list 'S))]
         ['impossible-member
          (membership 'S (nil-list 'S) 'selected)]]
        (explode
         (req nnrat-zero (app 'mass 'selected))
         'impossible-member))
       (function/lam
        [['head 'S] ['tail (list-of 'S)]
         ['induction-hypothesis (app motive 'tail)]
         ['selected 'S]
         ['distinct
          (no-duplicates
           'S
           (app (function/const* 'data/cons [data-u])
                'S 'head 'tail))]
         ['member
          (membership
           'S
           (app (function/const* 'data/cons [data-u])
                'S 'head 'tail)
           'selected)]]
        (let [head-same (eq-state 'S 'selected 'head)
              tail-member (membership 'S 'tail 'selected)
              head-not-in-tail
              (left-conjunct
               (proposition/negation
                (membership 'S 'tail 'head))
               (no-duplicates 'S 'tail) 'distinct)
              tail-distinct
              (right-conjunct
               (proposition/negation
                (membership 'S 'tail 'head))
               (no-duplicates 'S 'tail) 'distinct)
              spike-row
              (function/lam
               [['candidate 'S]]
               (diagonal-spike
                'S 'decision 'mass 'selected 'candidate))
              head-value
              (diagonal-spike 'S 'decision 'mass 'selected 'head)
              tail-total (map-sum 'S spike-row 'tail)
              row-total (radd head-value tail-total)
              target-mass (app 'mass 'selected)]
          (use-disjunction
           head-same tail-member
           (req row-total target-mass) 'member
           (function/lam
            [['same head-same]]
            (let [selected-not-in-tail
                  (function/lam
                   [['selected-member tail-member]]
                   (app
                    head-not-in-tail
                    (substitute-state
                     'S 'selected 'head 'same
                     (function/lam
                      [['candidate 'S]]
                      (membership 'S 'tail 'candidate))
                     'selected-member)))
                  head-is-mass
                  (app
                   (function/const*
                    'finite/nnrat-diagonal-spike-mass-of-equal [U])
                   'S 'decision 'mass 'certified
                   'selected 'head 'same)
                  tail-is-zero
                  (app
                   (function/const*
                    'finite/nnrat-map-sum-diagonal-spike-zero-of-not-member
                    [U])
                   'S 'decision 'mass 'certified 'tail
                   'selected selected-not-in-tail)]
              (equivalent-transitive
               row-total (radd target-mass nnrat-zero) target-mass
               (add-respects
                head-value target-mass tail-total nnrat-zero
                head-is-mass tail-is-zero)
               (app (function/const* 'nnrat/add-zero-right [])
                    target-mass))))
           (function/lam
            [['tail-has-selected tail-member]]
            (let [selected-not-head
                  (function/lam
                   [['same head-same]]
                   (app
                    head-not-in-tail
                    (substitute-state
                     'S 'selected 'head 'same
                     (function/lam
                      [['candidate 'S]]
                      (membership 'S 'tail 'candidate))
                     'tail-has-selected)))
                  head-is-zero
                  (app
                   (function/const*
                    'finite/nnrat-diagonal-spike-zero-of-different [U])
                   'S 'decision 'mass 'certified
                   'selected 'head selected-not-head)
                  tail-is-mass
                  (app 'induction-hypothesis 'selected
                       tail-distinct 'tail-has-selected)]
              (equivalent-transitive
               row-total (radd nnrat-zero target-mass) target-mass
               (add-respects
                head-value nnrat-zero tail-total target-mass
                head-is-zero tail-is-mass)
               (app (function/const* 'nnrat/add-zero-left [])
                    target-mass)))))))
       'items 'selected 'distinct 'member))}))

(def finset-diagonal-spike-total-spec
  {:name 'finite/nnrat-finset-diagonal-spike-total
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]
     ['member (membership 'S (enumeration 'S 'states) 'selected)]]
    (req
     (map-sum
      'S
      (function/lam
       [['candidate 'S]]
       (diagonal-spike 'S 'decision 'mass 'selected 'candidate))
      (enumeration 'S 'states))
     (app 'mass 'selected)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]
     ['member (membership 'S (enumeration 'S 'states) 'selected)]]
    (app
     (function/const*
      'finite/nnrat-map-sum-diagonal-spike-of-member-no-duplicates [U])
     'S 'decision 'mass 'certified
     (enumeration 'S 'states) 'selected
     (duplicate-free 'S 'states) 'member))})

(def finset-diagonal-spike-total-of-exhaustive-carrier-spec
  {:name 'finite/nnrat-finset-diagonal-spike-total-of-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S]]
    (req
     (map-sum
      'S
      (function/lam
       [['candidate 'S]]
       (diagonal-spike 'S 'decision 'mass 'selected 'candidate))
      (enumeration 'S 'states))
     (app 'mass 'selected)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['mass (function/arrow 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S]]
    (let [certified
          (app
           (function/const*
            'finite/certified-equality-of-exhaustive-carrier [U])
           'S 'states 'decision 'exhaustive)
          covered
          (app
           (function/const* 'finite/coverage-of-exhaustive-carrier [U])
           'S 'states 'decision 'exhaustive)]
      (app
       (function/const* 'finite/nnrat-finset-diagonal-spike-total [U])
       'S 'states 'decision 'mass certified
       'selected (app covered 'selected))))})

(def definition-specs
  [certified-equality-decision-spec
   certified-exhaustive-carrier-spec
   diagonal-spike-spec])
(def theorem-specs
  [certified-equality-of-exhaustive-carrier-spec
   coverage-of-exhaustive-carrier-spec
   diagonal-spike-zero-of-different-spec
   equality-decidable-of-certified-decision-spec
   diagonal-spike-mass-of-equal-spec
   diagonal-unit-spike-multiply-spec
   map-sum-diagonal-spike-zero-of-not-member-spec
   map-sum-diagonal-spike-of-member-no-duplicates-spec
   finset-diagonal-spike-total-spec
   finset-diagonal-spike-total-of-exhaustive-carrier-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.list-sum])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/add-zero-right :nnrat-diagonal-spike-support identities/add-zero-right-spec) (extend-spec-if-missing 'nnrat/add-zero-left :nnrat-diagonal-spike-support identities/add-zero-left-spec) (extend-spec-if-missing 'nnrat/multiply-zero-left :nnrat-diagonal-spike-support identities/multiply-zero-left-spec) (extend-spec-if-missing 'nnrat/multiply-one-left :nnrat-diagonal-spike-support identities/multiply-one-left-spec) (support/extend-with :nnrat-diagonal-spike (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.diagonal-spike))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
