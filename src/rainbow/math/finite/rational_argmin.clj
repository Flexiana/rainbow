(ns rainbow.math.finite.rational-argmin
  "Executable finite argmin with exact rational minimality certificates."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-argmax :as argmax]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- nil-list [element]
  (function/app (function/const* 'data/nil [data-level]) element))

(defn- cons-list [element head tail]
  (function/app (function/const* 'data/cons [data-level]) element head tail))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [U])
                element source value))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- rational-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- decide-at-most-rational [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level]) carrier value))

(defn- symmetric [level carrier left right same]
  (function/app (function/const* 'equality/symmetric [level])
                carrier left right same))

(defn- transitive-equality [level carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [level])
                carrier left middle right first second))

(defn- congruent
  [source-level target-level source target mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [source-level target-level])
   source target mapping left right same))

(defn- substitute [level carrier left right same predicate at-left]
  (function/app (function/const* 'equality/substitution [level])
                carrier left right same predicate at-left))

(defn- disjunction [left right]
  (proposition/disjunction left right))

(defn- select-min [element score left right]
  (function/app (function/const* 'decision/nnrat-select-min [U])
                element score left right))

(defn- argmin-from [element score initial source]
  (function/app (function/const* 'list/nnrat-argmin-from [U])
                element score initial source))

(defn- finite-argmin [element actions initial score]
  (function/app (function/const* 'decision/finite-nnrat-argmin [U])
                element actions initial score))

(defn- selected-min-at [element left right decision]
  (function/app (function/const* 'data/Bool.rec [data-level])
                (function/lam [['ignored bool]] element)
                right left decision))

(def select-min-spec
  {:name 'decision/nnrat-select-min
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['score (function/arrow 'A nnrat)]]
    (function/arrow 'A 'A 'A))
   :value
   (function/lam
    [['A type-u] ['score (function/arrow 'A nnrat)]
     ['left 'A] ['right 'A]]
    (function/app
     (function/const* 'data/Bool.rec [data-level])
     (function/lam [['ignored bool]] 'A)
     'right 'left
     (decide-at-most-rational
      (function/app 'score 'left)
      (function/app 'score 'right))))})

(def argmin-from-spec
  {:name 'list/nnrat-argmin-from
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['score (function/arrow 'A nnrat)]]
    (function/arrow 'A (list-of 'A) 'A))
   :value
   (function/lam
    [['A type-u] ['score (function/arrow 'A nnrat)]
     ['initial 'A] ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level data-level])
     'A
     (function/lam [['ignored (list-of 'A)]] 'A)
     'initial
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-best 'A]]
      (select-min 'A 'score 'head 'tail-best))
     'source))})

(def finite-argmin-spec
  {:name 'decision/finite-nnrat-argmin
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['actions (exact-finset-of 'A)]
     ['initial 'A] ['score (function/arrow 'A nnrat)]]
    'A)
   :value
   (function/lam
    [['A type-u] ['actions (exact-finset-of 'A)]
     ['initial 'A] ['score (function/arrow 'A nnrat)]]
    (argmin-from 'A 'score 'initial (enumeration 'A 'actions)))})

(def select-min-choice-spec
  (let [decision
        (decide-at-most-rational
         (function/app 'score 'left) (function/app 'score 'right))
        selected (selected-min-at 'A 'left 'right 'choice)
        motive
        (function/lam
         [['choice bool]]
         (disjunction
          (equality data-level 'A selected 'left)
          (equality data-level 'A selected 'right)))]
    {:name 'decision/nnrat-select-min-is-left-or-right
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (disjunction
       (equality data-level 'A (select-min 'A 'score 'left 'right) 'left)
       (equality data-level 'A (select-min 'A 'score 'left 'right) 'right)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (function/app
       (function/const* 'data/Bool.rec [zero-level])
       motive
       (function/app
        (function/const* 'proposition/right-disjunct [])
        (equality data-level 'A (selected-min-at 'A 'left 'right false-value)
                  'left)
        (equality data-level 'A (selected-min-at 'A 'left 'right false-value)
                  'right)
        (reflexive data-level 'A 'right))
       (function/app
        (function/const* 'proposition/left-disjunct [])
        (equality data-level 'A (selected-min-at 'A 'left 'right true-value)
                  'left)
        (equality data-level 'A (selected-min-at 'A 'left 'right true-value)
                  'right)
        (reflexive data-level 'A 'left))
       decision))}))

(def select-min-left-bound-spec
  (let [left-score (function/app 'score 'left)
        right-score (function/app 'score 'right)
        decision (decide-at-most-rational left-score right-score)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (equality type-level bool decision 'choice)
          (rational-at-most
           (function/app 'score
                         (selected-min-at 'A 'left 'right 'choice))
           left-score)))]
    {:name 'decision/nnrat-select-min-bounds-left
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (rational-at-most (function/app 'score
                                      (select-min 'A 'score 'left 'right))
                        left-score))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (function/app
       (function/app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        (function/lam
         [['same (equality type-level bool decision false-value)]]
         (function/app
          (function/const* 'nnrat/decide-at-most-false-reverse [])
          left-score right-score 'same))
        (function/lam
         [['ignored (equality type-level bool decision true-value)]]
         (function/app (function/const* 'nnrat/at-most-reflexive [])
                       left-score))
        decision)
       (reflexive type-level bool decision)))}))

(def select-min-right-bound-spec
  (let [left-score (function/app 'score 'left)
        right-score (function/app 'score 'right)
        decision (decide-at-most-rational left-score right-score)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (equality type-level bool decision 'choice)
          (rational-at-most
           (function/app 'score
                         (selected-min-at 'A 'left 'right 'choice))
           right-score)))]
    {:name 'decision/nnrat-select-min-bounds-right
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (rational-at-most (function/app 'score
                                      (select-min 'A 'score 'left 'right))
                        right-score))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (function/app
       (function/app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        (function/lam
         [['ignored (equality type-level bool decision false-value)]]
         (function/app (function/const* 'nnrat/at-most-reflexive [])
                       right-score))
        (function/lam
         [['same (equality type-level bool decision true-value)]]
         (function/app
          (function/const* 'nnrat/decide-at-most-true-sound [])
          left-score right-score 'same))
        decision)
       (reflexive type-level bool decision)))}))

(def argmin-from-initial-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (rational-at-most
          (function/app 'score (argmin-from 'A 'score 'initial 'source))
          (function/app 'score 'initial)))]
    {:name 'list/nnrat-argmin-from-bounded-by-initial
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]]
      (function/app motive 'source))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app (function/const* 'nnrat/at-most-reflexive [])
                     (function/app 'score 'initial))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [tail-best (argmin-from 'A 'score 'initial 'tail)
              selected (select-min 'A 'score 'head tail-best)]
          (function/app
           (function/const* 'nnrat/at-most-transitive [])
           (function/app 'score selected)
           (function/app 'score tail-best)
           (function/app 'score 'initial)
           (function/app
            (function/const* 'decision/nnrat-select-min-bounds-right [U])
            'A 'score 'head tail-best)
           'induction-hypothesis)))
       'source))}))

(def argmin-from-member-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (rational-at-most
           (function/app 'score
                         (argmin-from 'A 'score 'initial 'source))
           (function/app 'score 'value))))]
    {:name 'list/nnrat-argmin-from-bounded-by-member
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]
       ['value 'A] ['member (membership 'A 'source 'value)]]
      (rational-at-most
       (function/app 'score (argmin-from 'A 'score 'initial 'source))
       (function/app 'score 'value)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['value 'A] ['impossible (membership 'A (nil-list 'A) 'value)]]
        (function/app
         (function/const* 'proposition/explode [])
         (rational-at-most (function/app 'score 'initial)
                           (function/app 'score 'value))
         'impossible))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value 'A]
         ['member (membership 'A (cons-list 'A 'head 'tail) 'value)]]
        (let [tail-best (argmin-from 'A 'score 'initial 'tail)
              selected (select-min 'A 'score 'head tail-best)
              head-case (equality data-level 'A 'value 'head)
              tail-case (membership 'A 'tail 'value)
              target (rational-at-most (function/app 'score selected)
                                       (function/app 'score 'value))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (let [same-score
                  (congruent data-level type-level 'A nnrat 'score
                             'value 'head 'same)]
              (substitute
               type-level nnrat
               (function/app 'score 'head)
               (function/app 'score 'value)
               (symmetric type-level nnrat
                          (function/app 'score 'value)
                          (function/app 'score 'head)
                          same-score)
               (function/lam
                [['candidate nnrat]]
                (rational-at-most (function/app 'score selected)
                                  'candidate))
               (function/app
                (function/const* 'decision/nnrat-select-min-bounds-left [U])
                'A 'score 'head tail-best))))
           (function/lam
            [['tail-member tail-case]]
            (function/app
             (function/const* 'nnrat/at-most-transitive [])
             (function/app 'score selected)
             (function/app 'score tail-best)
             (function/app 'score 'value)
             (function/app
              (function/const* 'decision/nnrat-select-min-bounds-right [U])
              'A 'score 'head tail-best)
             (function/app 'induction-hypothesis 'value 'tail-member))))))
       'source))}))

(def argmin-from-origin-spec
  (let [result (argmin-from 'A 'score 'initial 'source)
        motive
        (function/lam
         [['source (list-of 'A)]]
         (disjunction
          (equality data-level 'A
                    (argmin-from 'A 'score 'initial 'source) 'initial)
          (membership 'A 'source
                      (argmin-from 'A 'score 'initial 'source))))]
    {:name 'list/nnrat-argmin-from-is-initial-or-member
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]]
      (disjunction
       (equality data-level 'A result 'initial)
       (membership 'A 'source result)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app
        (function/const* 'proposition/left-disjunct [])
        (equality data-level 'A 'initial 'initial)
        (membership 'A (nil-list 'A) 'initial)
        (reflexive data-level 'A 'initial))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (let [tail-best (argmin-from 'A 'score 'initial 'tail)
              selected (select-min 'A 'score 'head tail-best)
              selected-is-head (equality data-level 'A selected 'head)
              selected-is-tail (equality data-level 'A selected tail-best)
              target
              (disjunction
               (equality data-level 'A selected 'initial)
               (membership 'A (cons-list 'A 'head 'tail) selected))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           selected-is-head selected-is-tail target
           (function/app
            (function/const* 'decision/nnrat-select-min-is-left-or-right [U])
            'A 'score 'head tail-best)
           (function/lam
            [['same-head selected-is-head]]
            (function/app
             (function/const* 'proposition/right-disjunct [])
             (equality data-level 'A selected 'initial)
             (membership 'A (cons-list 'A 'head 'tail) selected)
             (function/app
              (function/const* 'proposition/left-disjunct [])
              selected-is-head
              (membership 'A 'tail selected)
              'same-head)))
           (function/lam
            [['same-tail selected-is-tail]]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             (equality data-level 'A tail-best 'initial)
             (membership 'A 'tail tail-best)
             target 'induction-hypothesis
             (function/lam
              [['tail-is-initial
                (equality data-level 'A tail-best 'initial)]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (equality data-level 'A selected 'initial)
               (membership 'A (cons-list 'A 'head 'tail) selected)
               (transitive-equality data-level 'A selected tail-best
                                    'initial 'same-tail 'tail-is-initial)))
             (function/lam
              [['tail-member (membership 'A 'tail tail-best)]]
              (let [selected-tail-member
                    (substitute
                     data-level 'A tail-best selected
                     (symmetric data-level 'A selected tail-best 'same-tail)
                     (function/lam
                      [['candidate 'A]] (membership 'A 'tail 'candidate))
                     'tail-member)]
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 (equality data-level 'A selected 'initial)
                 (membership 'A (cons-list 'A 'head 'tail) selected)
                 (function/app
                  (function/const* 'proposition/right-disjunct [])
                  (equality data-level 'A selected 'head)
                  (membership 'A 'tail selected)
                  selected-tail-member)))))))))
       'source))}))

(def finite-argmin-member-spec
  (let [result (finite-argmin 'A 'actions 'initial 'score)
        source (enumeration 'A 'actions)]
    {:name 'decision/finite-nnrat-argmin-is-member
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['initial-member (source-membership 'A 'actions 'initial)]]
      (source-membership 'A 'actions result))
     :value
     (function/lam
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['initial-member (source-membership 'A 'actions 'initial)]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       (equality data-level 'A result 'initial)
       (membership 'A source result)
       (membership 'A source result)
       (function/app
        (function/const* 'list/nnrat-argmin-from-is-initial-or-member [U])
        'A 'score 'initial source)
       (function/lam
        [['same (equality data-level 'A result 'initial)]]
        (substitute
         data-level 'A 'initial result
         (symmetric data-level 'A result 'initial 'same)
         (function/lam [['candidate 'A]]
                       (membership 'A source 'candidate))
         'initial-member))
       (function/lam
        [['member (membership 'A source result)]] 'member)))}))

(def finite-argmin-dominates-spec
  (let [result (finite-argmin 'A 'actions 'initial 'score)]
    {:name 'decision/finite-nnrat-argmin-dominates
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (rational-at-most (function/app 'score result)
                        (function/app 'score 'candidate)))
     :value
     (function/lam
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (function/app
       (function/const* 'list/nnrat-argmin-from-bounded-by-member [U])
       'A 'score 'initial (enumeration 'A 'actions)
       'candidate 'candidate-member))}))

(def definition-specs
  [select-min-spec argmin-from-spec finite-argmin-spec])

(def theorem-specs
  [select-min-choice-spec
   select-min-left-bound-spec
   select-min-right-bound-spec
   argmin-from-initial-bound-spec
   argmin-from-member-bound-spec
   argmin-from-origin-spec
   finite-argmin-member-spec
   finite-argmin-dominates-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite rational argmin expression failed elaboration"
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
          {:origin :native :producer :finite-rational-argmin}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite rational argmin declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      argmax/extend-environment
      extend-definitions
      extend-theorems))

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
