(ns rainbow.math.finite.signed-argmax
  "Executable finite argmax over exact signed-rational scores.

  The fold accepts an explicit fallback action, compares scores with the
  computable signed order, and returns an action rather than only a maximum
  value.  The certificates prove that the result comes from the declared
  finite carrier (when the fallback does) and dominates every declared action.
  Runtime carrier length and arbitrary signed scores are both supported.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.order-transitivity :as transitivity]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [data-level]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [data-level]) element head tail))
(defn- membership [element source value]
  (app (function/const* 'list/membership [U]) element source value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- source-membership [element source value]
  (app (function/const* 'finset-data/to-set [U]) element source value))
(defn- eq [level carrier left right]
  (function/equality level carrier left right))
(defn- eq-bool [left right] (eq type-level bool left right))
(defn- reflexive [level carrier value]
  (app (function/const* 'equality/reflexive [level]) carrier value))
(defn- symmetric [level carrier left right same]
  (app (function/const* 'equality/symmetric [level])
       carrier left right same))
(defn- transitive-eq [level carrier left middle right first second]
  (app (function/const* 'equality/transitive [level])
       carrier left middle right first second))
(defn- congruent [source-level target-level source target mapping left right same]
  (app (function/const* 'equality/congruent-function
                        [source-level target-level])
       source target mapping left right same))
(defn- substitute [level carrier left right same predicate at-left]
  (app (function/const* 'equality/substitution [level])
       carrier left right same predicate at-left))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- decide [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- select [element score left right]
  (app (function/const* 'decision/signed-select [U])
       element score left right))
(defn- argmax-from [element score initial source]
  (app (function/const* 'list/signed-argmax-from [U])
       element score initial source))
(defn- finite-argmax [element actions initial score]
  (app (function/const* 'decision/finite-signed-argmax [U])
       element actions initial score))
(defn- selected-at [element left right choice]
  (app (function/const* 'data/Bool.rec [data-level])
       (function/lam [['ignored bool]] element)
       left right choice))
(defn- disjunction [left right]
  (proposition/disjunction left right))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))

(def select-spec
  {:name 'decision/signed-select :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['score (function/arrow 'A signed)]]
    (function/arrow 'A 'A 'A))
   :value
   (function/lam
    [['A type-u] ['score (function/arrow 'A signed)]
     ['left 'A] ['right 'A]]
    (selected-at
     'A 'left 'right
     (decide (app 'score 'left) (app 'score 'right))))})

(def argmax-from-spec
  {:name 'list/signed-argmax-from :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['score (function/arrow 'A signed)]]
    (function/arrow 'A (list-of 'A) 'A))
   :value
   (function/lam
    [['A type-u] ['score (function/arrow 'A signed)]
     ['initial 'A] ['source (list-of 'A)]]
    (app
     (function/const* 'data/List.rec [data-level data-level])
     'A
     (function/lam [['ignored (list-of 'A)]] 'A)
     'initial
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-best 'A]]
      (select 'A 'score 'head 'tail-best))
     'source))})

(def finite-argmax-spec
  {:name 'decision/finite-signed-argmax :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['actions (exact-finset-of 'A)]
     ['initial 'A] ['score (function/arrow 'A signed)]]
    'A)
   :value
   (function/lam
    [['A type-u] ['actions (exact-finset-of 'A)]
     ['initial 'A] ['score (function/arrow 'A signed)]]
    (argmax-from 'A 'score 'initial (enumeration 'A 'actions)))})

(def select-choice-spec
  (let [decision (decide (app 'score 'left) (app 'score 'right))
        selected (selected-at 'A 'left 'right 'choice)
        motive
        (function/lam
         [['choice bool]]
         (disjunction
          (eq data-level 'A selected 'left)
          (eq data-level 'A selected 'right)))]
    {:name 'decision/signed-select-is-left-or-right :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A signed)]
       ['left 'A] ['right 'A]]
      (disjunction
       (eq data-level 'A (select 'A 'score 'left 'right) 'left)
       (eq data-level 'A (select 'A 'score 'left 'right) 'right)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A signed)]
       ['left 'A] ['right 'A]]
      (app
       (function/const* 'data/Bool.rec [zero-level])
       motive
       (app (function/const* 'proposition/left-disjunct [])
            (eq data-level 'A (selected-at 'A 'left 'right false-value) 'left)
            (eq data-level 'A (selected-at 'A 'left 'right false-value) 'right)
            (reflexive data-level 'A 'left))
       (app (function/const* 'proposition/right-disjunct [])
            (eq data-level 'A (selected-at 'A 'left 'right true-value) 'left)
            (eq data-level 'A (selected-at 'A 'left 'right true-value) 'right)
            (reflexive data-level 'A 'right))
       decision))}))

(defn- select-bound-spec [left?]
  (let [left-score (app 'score 'left)
        right-score (app 'score 'right)
        decision (decide left-score right-score)
        source-score (if left? left-score right-score)
        name (if left?
               'decision/signed-select-left-bound
               'decision/signed-select-right-bound)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (eq-bool decision 'choice)
          (sle source-score
               (app 'score (selected-at 'A 'left 'right 'choice)))))]
    {:name name :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A signed)]
       ['left 'A] ['right 'A]]
      (sle source-score (app 'score (select 'A 'score 'left 'right))))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A signed)]
       ['left 'A] ['right 'A]]
      (app
       (app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        (function/lam
         [['decided-false (eq-bool decision false-value)]]
         (if left?
           (order-reflexive left-score)
           (app (function/const*
                 'signed/decide-at-most-false-reverse [])
                left-score right-score 'decided-false)))
        (function/lam
         [['decided-true (eq-bool decision true-value)]]
         (if left?
           (app (function/const* 'signed/decide-at-most-true-sound [])
                left-score right-score 'decided-true)
           (order-reflexive right-score)))
        decision)
       (reflexive type-level bool decision)))}))

(def select-left-bound-spec (select-bound-spec true))
(def select-right-bound-spec (select-bound-spec false))

(def argmax-from-initial-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (sle
          (app 'score 'initial)
          (app 'score (argmax-from 'A 'score 'initial 'source))))]
    {:name 'list/signed-argmax-from-bounds-initial :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]]
      (app motive 'source))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (order-reflexive (app 'score 'initial))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (app motive 'tail)]]
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)]
          (order-transitive
           (app 'score 'initial)
           (app 'score tail-best)
           (app 'score (select 'A 'score 'head tail-best))
           'induction-hypothesis
           (app (function/const*
                 'decision/signed-select-right-bound [U])
                'A 'score 'head tail-best))))
       'source))}))

(def argmax-from-member-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (sle
           (app 'score 'value)
           (app 'score (argmax-from 'A 'score 'initial 'source)))))]
    {:name 'list/signed-argmax-from-bounds-member :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]
       ['value 'A] ['member (membership 'A 'source 'value)]]
      (sle (app 'score 'value)
           (app 'score (argmax-from 'A 'score 'initial 'source))))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['value 'A] ['impossible (membership 'A (nil-list 'A) 'value)]]
        (app (function/const* 'proposition/explode [])
             (sle (app 'score 'value) (app 'score 'initial))
             'impossible))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (app motive 'tail)]
         ['value 'A]
         ['member (membership 'A (cons-list 'A 'head 'tail) 'value)]]
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)
              selected (select 'A 'score 'head tail-best)
              head-case (eq data-level 'A 'value 'head)
              tail-case (membership 'A 'tail 'value)
              target (sle (app 'score 'value) (app 'score selected))]
          (app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (let [score-same
                  (congruent data-level type-level 'A signed 'score
                             'value 'head 'same)
                  head-bound
                  (app (function/const*
                        'decision/signed-select-left-bound [U])
                       'A 'score 'head tail-best)]
              (substitute
               type-level signed
               (app 'score 'head) (app 'score 'value)
               (symmetric type-level signed
                          (app 'score 'value) (app 'score 'head) score-same)
               (function/lam
                [['candidate signed]] (sle 'candidate (app 'score selected)))
               head-bound)))
           (function/lam
            [['tail-member tail-case]]
            (order-transitive
             (app 'score 'value)
             (app 'score tail-best)
             (app 'score selected)
             (app 'induction-hypothesis 'value 'tail-member)
             (app (function/const*
                   'decision/signed-select-right-bound [U])
                  'A 'score 'head tail-best))))))
       'source))}))

(def argmax-from-origin-spec
  (let [result (argmax-from 'A 'score 'initial 'source)
        motive
        (function/lam
         [['source (list-of 'A)]]
         (disjunction
          (eq data-level 'A (argmax-from 'A 'score 'initial 'source) 'initial)
          (membership 'A 'source
                      (argmax-from 'A 'score 'initial 'source))))]
    {:name 'list/signed-argmax-from-is-initial-or-member :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]]
      (disjunction
       (eq data-level 'A result 'initial)
       (membership 'A 'source result)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A signed)]
       ['initial 'A] ['source (list-of 'A)]]
      (app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (app (function/const* 'proposition/left-disjunct [])
            (eq data-level 'A 'initial 'initial)
            (membership 'A (nil-list 'A) 'initial)
            (reflexive data-level 'A 'initial))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (app motive 'tail)]]
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)
              selected (select 'A 'score 'head tail-best)
              selected-head (eq data-level 'A selected 'head)
              selected-tail (eq data-level 'A selected tail-best)
              target
              (disjunction
               (eq data-level 'A selected 'initial)
               (membership 'A (cons-list 'A 'head 'tail) selected))]
          (app
           (function/const* 'proposition/use-disjunction [])
           selected-head selected-tail target
           (app (function/const*
                 'decision/signed-select-is-left-or-right [U])
                'A 'score 'head tail-best)
           (function/lam
            [['same-head selected-head]]
            (app
             (function/const* 'proposition/right-disjunct [])
             (eq data-level 'A selected 'initial)
             (membership 'A (cons-list 'A 'head 'tail) selected)
             (app (function/const* 'proposition/left-disjunct [])
                  selected-head (membership 'A 'tail selected) 'same-head)))
           (function/lam
            [['same-tail selected-tail]]
            (app
             (function/const* 'proposition/use-disjunction [])
             (eq data-level 'A tail-best 'initial)
             (membership 'A 'tail tail-best)
             target 'induction-hypothesis
             (function/lam
              [['tail-initial (eq data-level 'A tail-best 'initial)]]
              (app
               (function/const* 'proposition/left-disjunct [])
               (eq data-level 'A selected 'initial)
               (membership 'A (cons-list 'A 'head 'tail) selected)
               (transitive-eq data-level 'A selected tail-best 'initial
                              'same-tail 'tail-initial)))
             (function/lam
              [['tail-member (membership 'A 'tail tail-best)]]
              (let [selected-member
                    (substitute
                     data-level 'A tail-best selected
                     (symmetric data-level 'A selected tail-best 'same-tail)
                     (function/lam
                      [['candidate 'A]] (membership 'A 'tail 'candidate))
                     'tail-member)]
                (app
                 (function/const* 'proposition/right-disjunct [])
                 (eq data-level 'A selected 'initial)
                 (membership 'A (cons-list 'A 'head 'tail) selected)
                 (app (function/const* 'proposition/right-disjunct [])
                      (eq data-level 'A selected 'head)
                      (membership 'A 'tail selected)
                      selected-member)))))))))
       'source))}))

(def finite-argmax-member-spec
  (let [result (finite-argmax 'A 'actions 'initial 'score)
        source (enumeration 'A 'actions)]
    {:name 'decision/finite-signed-argmax-is-member :universes ['u]
     :type
     (function/forall
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A signed)]
       ['initial-member (source-membership 'A 'actions 'initial)]]
      (source-membership 'A 'actions result))
     :value
     (function/lam
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A signed)]
       ['initial-member (source-membership 'A 'actions 'initial)]]
      (app
       (function/const* 'proposition/use-disjunction [])
       (eq data-level 'A result 'initial)
       (membership 'A source result)
       (membership 'A source result)
       (app (function/const*
             'list/signed-argmax-from-is-initial-or-member [U])
            'A 'score 'initial source)
       (function/lam
        [['same (eq data-level 'A result 'initial)]]
        (substitute
         data-level 'A 'initial result
         (symmetric data-level 'A result 'initial 'same)
         (function/lam [['candidate 'A]] (membership 'A source 'candidate))
         'initial-member))
       (function/lam
        [['member (membership 'A source result)]] 'member)))}))

(def finite-argmax-dominates-spec
  (let [result (finite-argmax 'A 'actions 'initial 'score)]
    {:name 'decision/finite-signed-argmax-dominates :universes ['u]
     :type
     (function/forall
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A signed)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (sle (app 'score 'candidate) (app 'score result)))
     :value
     (function/lam
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A signed)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (app
       (function/const* 'list/signed-argmax-from-bounds-member [U])
       'A 'score 'initial (enumeration 'A 'actions)
       'candidate 'candidate-member))}))

(def definition-specs [select-spec argmax-from-spec finite-argmax-spec])
(def theorem-specs
  [select-choice-spec select-left-bound-spec select-right-bound-spec
   argmax-from-initial-bound-spec argmax-from-member-bound-spec
   argmax-from-origin-spec finite-argmax-member-spec
   finite-argmax-dominates-spec])

(defn extend-environment [env]
  (-> env
      transitivity/extend-environment
      minmax/extend-environment
      (support/extend-with
       :finite-signed-argmax (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
