(ns rainbow.math.finite.rational-argmax
  "Executable finite argmax with exact rational dominance certificates."
  (:refer-clojure :exclude [denominator numerator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value] (function/app successor value))
(defn- numeral [value] (nth (iterate succ zero) value))
(def one (numeral 1))
(def two (numeral 2))
(def three (numeral 3))
(def four (numeral 4))
(def ten (numeral 10))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- nil-list [element]
  (function/app (function/const* 'data/nil [data-level]) element))

(defn- cons-list [element head tail]
  (function/app (function/const* 'data/cons [data-level])
                element head tail))

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

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- nat-at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- decide-at-most-nat [left right]
  (function/app (function/const* 'nat/decide-at-most []) left right))

(defn- rational-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- decide-at-most-rational [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most [])
                left right))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level])
                carrier value))

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

(defn- zero-at-most [right]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['extra nat]]
                 (equality type-level nat (add zero 'extra) right))
   right
   (reflexive type-level nat right)))

(defn- select [element score left right]
  (function/app (function/const* 'decision/nnrat-select [U])
                element score left right))

(defn- argmax-from [element score initial source]
  (function/app (function/const* 'list/nnrat-argmax-from [U])
                element score initial source))

(defn- finite-argmax [element actions initial score]
  (function/app (function/const* 'decision/finite-nnrat-argmax [U])
                element actions initial score))

(defn- selected-at [element left right decision]
  (function/app (function/const* 'data/Bool.rec [data-level])
                (function/lam [['ignored bool]] element)
                left right decision))

(defn- disjunction [left right]
  (proposition/disjunction left right))

(def bool-false-not-true-spec
  (let [predicate
        (function/lam
         [['value bool]]
         (function/app
          (function/const* 'data/Bool.rec [type-level])
          (function/lam [['ignored bool]] 'Prop)
          (proposition/truth) (proposition/falsity) 'value))]
    {:name 'bool/false-not-true
     :universes []
     :type
     (function/arrow
      (equality type-level bool false-value true-value)
      (proposition/falsity))
     :value
     (function/lam
      [['same (equality type-level bool false-value true-value)]]
      (function/app 'same predicate
                    (function/const* 'proposition/trivial [])))}))

(def bool-true-not-false-spec
  (let [predicate
        (function/lam
         [['value bool]]
         (function/app
          (function/const* 'data/Bool.rec [type-level])
          (function/lam [['ignored bool]] 'Prop)
          (proposition/falsity) (proposition/truth) 'value))]
    {:name 'bool/true-not-false
     :universes []
     :type
     (function/arrow
      (equality type-level bool true-value false-value)
      (proposition/falsity))
     :value
     (function/lam
      [['same (equality type-level bool true-value false-value)]]
      (function/app 'same predicate
                    (function/const* 'proposition/trivial [])))}))

(def nat-decide-at-most-true-sound-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]
           ['same (equality type-level bool
                            (decide-at-most-nat 'left 'right)
                            true-value)]]
          (nat-at-most 'left 'right)))]
    {:name 'nat/decide-at-most-true-sound
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]
       ['same (equality type-level bool
                        (decide-at-most-nat 'left 'right) true-value)]]
      (nat-at-most 'left 'right))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]
         ['ignored (equality type-level bool
                             (decide-at-most-nat zero 'right) true-value)]]
        (zero-at-most 'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/arrow
           (equality type-level bool
                     (decide-at-most-nat (succ 'left-previous) 'candidate)
                     true-value)
           (nat-at-most (succ 'left-previous) 'candidate)))
         (function/lam
          [['impossible
            (equality type-level bool false-value true-value)]]
          (function/app
           (function/const* 'proposition/explode [])
           (nat-at-most (succ 'left-previous) zero)
           (function/app (function/const* 'bool/false-not-true [])
                         'impossible)))
         (function/lam
          [['right-previous nat]
           ['ignored-previous-proof
            (function/arrow
             (equality type-level bool
                       (decide-at-most-nat (succ 'left-previous)
                                           'right-previous)
                       true-value)
             (nat-at-most (succ 'left-previous) 'right-previous))]
           ['same
            (equality type-level bool
                      (decide-at-most-nat 'left-previous 'right-previous)
                      true-value)]]
          (function/app
           (function/const* 'nat/add-left-monotone [])
           one 'left-previous 'right-previous
           (function/app 'induction-hypothesis 'right-previous 'same)))
         'right))
       'left))}))

(def nat-decide-at-most-false-reverse-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]
           ['same (equality type-level bool
                            (decide-at-most-nat 'left 'right)
                            false-value)]]
          (nat-at-most 'right 'left)))]
    {:name 'nat/decide-at-most-false-reverse
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]
       ['same (equality type-level bool
                        (decide-at-most-nat 'left 'right) false-value)]]
      (nat-at-most 'right 'left))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]
         ['impossible (equality type-level bool true-value false-value)]]
        (function/app
         (function/const* 'proposition/explode [])
         (nat-at-most 'right zero)
         (function/app (function/const* 'bool/true-not-false [])
                       'impossible)))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/arrow
           (equality type-level bool
                     (decide-at-most-nat (succ 'left-previous) 'candidate)
                     false-value)
           (nat-at-most 'candidate (succ 'left-previous))))
         (function/lam
          [['ignored (equality type-level bool false-value false-value)]]
          (zero-at-most (succ 'left-previous)))
         (function/lam
          [['right-previous nat]
           ['ignored-previous-proof
            (function/arrow
             (equality type-level bool
                       (decide-at-most-nat (succ 'left-previous)
                                           'right-previous)
                       false-value)
             (nat-at-most 'right-previous (succ 'left-previous)))]
           ['same
            (equality type-level bool
                      (decide-at-most-nat 'left-previous 'right-previous)
                      false-value)]]
          (function/app
           (function/const* 'nat/add-left-monotone [])
           one 'right-previous 'left-previous
           (function/app 'induction-hypothesis 'right-previous 'same)))
         'right))
       'left))}))

(def at-most-rewrite-left-spec
  {:name 'nnrat/at-most-rewrite-left
   :universes []
   :type
   (function/forall
    [['left nnrat] ['equivalent-left nnrat] ['right nnrat]
     ['same (equality type-level nnrat 'left 'equivalent-left)]
     ['ordered (rational-at-most 'equivalent-left 'right)]]
    (rational-at-most 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['equivalent-left nnrat] ['right nnrat]
     ['same (equality type-level nnrat 'left 'equivalent-left)]
     ['ordered (rational-at-most 'equivalent-left 'right)]]
    (substitute
     type-level nnrat 'equivalent-left 'left
     (symmetric type-level nnrat 'left 'equivalent-left 'same)
     (function/lam [['candidate nnrat]]
                   (rational-at-most 'candidate 'right))
     'ordered))})

(def nnrat-decide-at-most-true-sound-spec
  {:name 'nnrat/decide-at-most-true-sound
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (equality type-level bool
                      (decide-at-most-rational 'left 'right) true-value)]]
    (rational-at-most 'left 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (equality type-level bool
                      (decide-at-most-rational 'left 'right) true-value)]]
    (function/app
     (function/const* 'nnrat/at-most-from-cross [])
     'left 'right
     (function/app
      (function/const* 'nat/decide-at-most-true-sound [])
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'left)
       (function/app (function/const* 'nnrat/denominator []) 'right))
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'right)
       (function/app (function/const* 'nnrat/denominator []) 'left))
      'same)))})

(def nnrat-decide-at-most-false-reverse-spec
  {:name 'nnrat/decide-at-most-false-reverse
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (equality type-level bool
                      (decide-at-most-rational 'left 'right) false-value)]]
    (rational-at-most 'right 'left))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (equality type-level bool
                      (decide-at-most-rational 'left 'right) false-value)]]
    (function/app
     (function/const* 'nnrat/at-most-from-cross [])
     'right 'left
     (function/app
      (function/const* 'nat/decide-at-most-false-reverse [])
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'left)
       (function/app (function/const* 'nnrat/denominator []) 'right))
      (function/app
       (function/const* 'nat/multiply [])
       (function/app (function/const* 'nnrat/numerator []) 'right)
       (function/app (function/const* 'nnrat/denominator []) 'left))
      'same)))})

(def select-spec
  {:name 'decision/nnrat-select
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
     'left 'right
     (decide-at-most-rational
      (function/app 'score 'left)
      (function/app 'score 'right))))})

(def argmax-from-spec
  {:name 'list/nnrat-argmax-from
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
      (select 'A 'score 'head 'tail-best))
     'source))})

(def finite-argmax-spec
  {:name 'decision/finite-nnrat-argmax
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
    (argmax-from 'A 'score 'initial (enumeration 'A 'actions)))})

(def select-choice-spec
  (let [decision
        (decide-at-most-rational
         (function/app 'score 'left) (function/app 'score 'right))
        selected (selected-at 'A 'left 'right 'choice)
        motive
        (function/lam
         [['choice bool]]
         (disjunction
          (equality data-level 'A selected 'left)
          (equality data-level 'A selected 'right)))]
    {:name 'decision/nnrat-select-is-left-or-right
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (disjunction
       (equality data-level 'A (select 'A 'score 'left 'right) 'left)
       (equality data-level 'A (select 'A 'score 'left 'right) 'right)))
     :value
     (function/lam
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (function/app
       (function/const* 'data/Bool.rec [zero-level])
       motive
       (function/app
        (function/const* 'proposition/left-disjunct [])
        (equality data-level 'A (selected-at 'A 'left 'right false-value)
                  'left)
        (equality data-level 'A (selected-at 'A 'left 'right false-value)
                  'right)
        (reflexive data-level 'A 'left))
       (function/app
        (function/const* 'proposition/right-disjunct [])
        (equality data-level 'A (selected-at 'A 'left 'right true-value)
                  'left)
        (equality data-level 'A (selected-at 'A 'left 'right true-value)
                  'right)
        (reflexive data-level 'A 'right))
       decision))}))

(def select-left-bound-spec
  (let [left-score (function/app 'score 'left)
        right-score (function/app 'score 'right)
        decision (decide-at-most-rational left-score right-score)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (equality type-level bool decision 'choice)
          (rational-at-most
           left-score
           (function/app
            'score (selected-at 'A 'left 'right 'choice)))))]
    {:name 'decision/nnrat-select-left-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (rational-at-most left-score (function/app 'score
                                                 (select 'A 'score
                                                         'left 'right))))
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
                       left-score))
        (function/lam
         [['same (equality type-level bool decision true-value)]]
         (function/app
          (function/const* 'nnrat/decide-at-most-true-sound [])
          left-score right-score 'same))
        decision)
       (reflexive type-level bool decision)))}))

(def select-right-bound-spec
  (let [left-score (function/app 'score 'left)
        right-score (function/app 'score 'right)
        decision (decide-at-most-rational left-score right-score)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (equality type-level bool decision 'choice)
          (rational-at-most
           right-score
           (function/app
            'score (selected-at 'A 'left 'right 'choice)))))]
    {:name 'decision/nnrat-select-right-bound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['left 'A] ['right 'A]]
      (rational-at-most right-score (function/app 'score
                                                  (select 'A 'score
                                                          'left 'right))))
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
                       right-score))
        decision)
       (reflexive type-level bool decision)))}))

(def argmax-from-initial-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (rational-at-most
          (function/app 'score 'initial)
          (function/app 'score
                        (argmax-from 'A 'score 'initial 'source))))]
    {:name 'list/nnrat-argmax-from-bounds-initial
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
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)]
          (function/app
           (function/const* 'nnrat/at-most-transitive [])
           (function/app 'score 'initial)
           (function/app 'score tail-best)
           (function/app 'score (select 'A 'score 'head tail-best))
           'induction-hypothesis
           (function/app
            (function/const* 'decision/nnrat-select-right-bound [U])
            'A 'score 'head tail-best))))
       'source))}))

(def argmax-from-member-bound-spec
  (let [motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (membership 'A 'source 'value)]]
          (rational-at-most
           (function/app 'score 'value)
           (function/app 'score
                         (argmax-from 'A 'score 'initial 'source)))))]
    {:name 'list/nnrat-argmax-from-bounds-member
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['score (function/arrow 'A nnrat)]
       ['initial 'A] ['source (list-of 'A)]
       ['value 'A] ['member (membership 'A 'source 'value)]]
      (rational-at-most
       (function/app 'score 'value)
       (function/app 'score (argmax-from 'A 'score 'initial 'source))))
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
         (rational-at-most (function/app 'score 'value)
                           (function/app 'score 'initial))
         'impossible))
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value 'A]
         ['member (membership 'A (cons-list 'A 'head 'tail) 'value)]]
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)
              selected (select 'A 'score 'head tail-best)
              head-case (equality data-level 'A 'value 'head)
              tail-case (membership 'A 'tail 'value)
              target (rational-at-most (function/app 'score 'value)
                                       (function/app 'score selected))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'member
           (function/lam
            [['same head-case]]
            (function/app
             (function/const* 'nnrat/at-most-rewrite-left [])
             (function/app 'score 'value)
             (function/app 'score 'head)
             (function/app 'score selected)
             (congruent data-level type-level 'A nnrat 'score
                        'value 'head 'same)
             (function/app
              (function/const* 'decision/nnrat-select-left-bound [U])
              'A 'score 'head tail-best)))
           (function/lam
            [['tail-member tail-case]]
            (function/app
             (function/const* 'nnrat/at-most-transitive [])
             (function/app 'score 'value)
             (function/app 'score tail-best)
             (function/app 'score selected)
             (function/app 'induction-hypothesis 'value 'tail-member)
             (function/app
              (function/const* 'decision/nnrat-select-right-bound [U])
              'A 'score 'head tail-best))))))
       'source))}))

(def argmax-from-origin-spec
  (let [result (argmax-from 'A 'score 'initial 'source)
        motive
        (function/lam
         [['source (list-of 'A)]]
         (disjunction
          (equality data-level 'A
                    (argmax-from 'A 'score 'initial 'source) 'initial)
          (membership 'A 'source
                      (argmax-from 'A 'score 'initial 'source))))]
    {:name 'list/nnrat-argmax-from-is-initial-or-member
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
        (let [tail-best (argmax-from 'A 'score 'initial 'tail)
              selected (select 'A 'score 'head tail-best)
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
            (function/const* 'decision/nnrat-select-is-left-or-right [U])
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

(def finite-argmax-member-spec
  (let [result (finite-argmax 'A 'actions 'initial 'score)
        source (enumeration 'A 'actions)]
    {:name 'decision/finite-nnrat-argmax-is-member
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
        (function/const* 'list/nnrat-argmax-from-is-initial-or-member [U])
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

(def finite-argmax-dominates-spec
  (let [result (finite-argmax 'A 'actions 'initial 'score)]
    {:name 'decision/finite-nnrat-argmax-dominates
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (rational-at-most (function/app 'score 'candidate)
                        (function/app 'score result)))
     :value
     (function/lam
      [['A type-u] ['actions (exact-finset-of 'A)]
       ['initial 'A] ['score (function/arrow 'A nnrat)]
       ['candidate 'A]
       ['candidate-member (source-membership 'A 'actions 'candidate)]]
      (function/app
       (function/const* 'list/nnrat-argmax-from-bounds-member [U])
       'A 'score 'initial (enumeration 'A 'actions)
       'candidate 'candidate-member))}))

(def definition-specs
  [select-spec argmax-from-spec finite-argmax-spec])

(def theorem-specs
  [bool-false-not-true-spec bool-true-not-false-spec
   nat-decide-at-most-true-sound-spec
   nat-decide-at-most-false-reverse-spec
   at-most-rewrite-left-spec
   nnrat-decide-at-most-true-sound-spec
   nnrat-decide-at-most-false-reverse-spec
   select-choice-spec select-left-bound-spec select-right-bound-spec
   argmax-from-initial-bound-spec argmax-from-member-bound-spec
   argmax-from-origin-spec finite-argmax-member-spec
   finite-argmax-dominates-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite rational argmax expression failed elaboration"
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
          {:origin :native :producer :finite-rational-argmax}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite rational argmax declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-definitions extend-theorems))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.rational-argmax))
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
