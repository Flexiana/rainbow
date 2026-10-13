(ns rainbow.math.finite.index
  "Axiom-free bounded indices as a structural finite family.

  `finite/Index 0` is a recursive-only empty data type (it has no base
  constructor) and
  `finite/Index (n+1)` is `Option (finite/Index n)`.  Thus the last index is
  `none` and weakening an earlier index is `some`.  Unlike a proof-carrying
  subtype of Nat, this representation needs no proof-irrelevance axiom for
  equality and is suitable for executable finite tables.

  This first layer supplies the family, its constructors, and the complete
  successor case split.  Enumeration and certified equality build on that
  structural split.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.diagonal-spike :as diagonal-spike]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def kind-level [:succ type-level])
(def type-sort [:sort type-level])
(def nat (function/const* 'data/Nat []))
(def succ (function/const* 'data/succ []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(def empty-block-spec
  {:block/schema-version 1
   :block/alias 'finite/Empty
   :block/universes []
   :block/parameters []
   :block/sort-level type-level
   :block/constructors
   [{:constructor/alias 'finite/empty-step
     :constructor/fields
     [{:field/name 'previous :field/type [:self]}]}]})

(defn- app [f & xs] (apply function/app f xs))
(defn- index-of [upper]
  (app (function/const* 'finite/Index []) upper))
(defn- option-of [element]
  (app (function/const* 'data/Option [type-level]) element))
(defn- list-of [element]
  (app (function/const* 'data/List [type-level]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [type-level]) element))
(defn- cons-list [element head tail]
  (app (function/const* 'data/cons [type-level]) element head tail))
(defn- map-list [source target mapping items]
  (app (function/const* 'list/map [type-level type-level])
       source target mapping items))
(defn- membership [element items value]
  (app (function/const* 'list/membership [zero-level])
       element items value))
(defn- no-duplicates [element items]
  (app (function/const* 'list/no-duplicates [zero-level]) element items))
(defn- finset-of [element]
  (app (function/const* 'finset-data/Finset [zero-level]) element))
(defn- finset-enumeration [element source]
  (app (function/const* 'finset-data/enumeration [zero-level])
       element source))
(defn- last-index [upper]
  (app (function/const* 'finite/index-last []) upper))
(defn- weaken-index [upper source]
  (app (function/const* 'finite/index-weaken []) upper source))
(defn- index-enumeration [upper]
  (app (function/const* 'finite/index-enumeration []) upper))
(defn- index-equality [upper left right]
  (function/equality type-level (index-of upper) left right))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))
(defn- decide-index-equality [upper left right]
  (app (function/const* 'finite/index-decide-equality [])
       upper left right))
(defn- equality-soundness [element decision]
  (function/forall
   [['left element] ['right element]
    ['accepted
     (bool-equality (app decision 'left 'right) true-value)]]
   (function/equality type-level element 'left 'right)))
(defn- equality-completeness [element decision]
  (function/forall
   [['left element] ['right element]
    ['same (function/equality type-level element 'left 'right)]]
   (bool-equality (app decision 'left 'right) true-value)))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [zero-level])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [zero-level])
       element states decision))
(defn- option-eliminate [element result fallback present source]
  (app (function/const* 'data/Option.rec [type-level type-level])
       element
       (function/lam [['ignored (option-of element)]] result)
       fallback present source))
(defn- false-not-true [same]
  (let [predicate
        (function/lam
         [['value bool]]
         (app (function/const* 'data/Bool.rec [type-level])
              (function/lam [['ignored bool]] 'Prop)
              (proposition/truth) (proposition/falsity) 'value))]
    (app same predicate
         (function/const* 'proposition/trivial []))))

(def index-spec
  {:name 'finite/Index
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat type-sort)
   :value
   (function/lam
    [['upper nat]]
    (app
     (function/const* 'data/Nat.rec [kind-level])
     (function/lam [['ignored nat]] type-sort)
     (function/const* 'finite/Empty [])
     (function/lam
      [['previous nat] ['prior type-sort]]
      (option-of 'prior))
     'upper))})

(def index-last-spec
  {:name 'finite/index-last
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/forall
    [['upper nat]] (index-of (app succ 'upper)))
   :value
   (function/lam
    [['upper nat]]
    (app (function/const* 'data/none [type-level])
         (index-of 'upper)))})

(def index-weaken-spec
  {:name 'finite/index-weaken
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/forall
    [['upper nat] ['source (index-of 'upper)]]
    (index-of (app succ 'upper)))
   :value
   (function/lam
    [['upper nat] ['source (index-of 'upper)]]
    (app (function/const* 'data/some [type-level])
         (index-of 'upper) 'source))})

(def index-enumeration-spec
  {:name 'finite/index-enumeration
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/forall
    [['upper nat]] (list-of (index-of 'upper)))
   :value
   (function/lam
    [['upper nat]]
    (app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam
      [['bound nat]] (list-of (index-of 'bound)))
     (nil-list (index-of (function/const* 'data/zero [])))
     (function/lam
      [['previous nat]
       ['prior-enumeration (list-of (index-of 'previous))]]
      (let [prior (index-of 'previous)
            current (index-of (app succ 'previous))
            weaken
            (function/lam
             [['source prior]] (weaken-index 'previous 'source))]
        (cons-list
         current (last-index 'previous)
         (map-list prior current weaken 'prior-enumeration))))
     'upper))})

(def index-decide-equality-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (function/arrow (index-of 'upper) (index-of 'upper) bool))]
    {:name 'finite/index-decide-equality
     :kind :definition
     :universes []
     :transparency :reducible
     :type
     (function/forall
      [['upper nat]]
      (function/arrow (index-of 'upper) (index-of 'upper) bool))
     :value
     (function/lam
      [['upper nat]]
      (app
       (function/const* 'data/Nat.rec [type-level])
       motive
       (let [empty (index-of (function/const* 'data/zero []))]
         (function/lam
          [['left empty] ['right empty]]
          (app
           (function/const* 'finite/Empty.rec [type-level])
           (function/lam [['candidate empty]] bool)
           (function/lam
            [['previous empty] ['induction-hypothesis bool]]
            'induction-hypothesis)
           'left)))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (app motive 'previous)]]
        (let [prior (index-of 'previous)
              current (index-of (app succ 'previous))]
          (function/lam
           [['left current] ['right current]]
           (option-eliminate
            prior bool
            (option-eliminate
             prior bool true-value
             (function/lam [['ignored prior]] false-value)
             'right)
            (function/lam
             [['left-value prior]]
             (option-eliminate
              prior bool false-value
              (function/lam
               [['right-value prior]]
               (app 'induction-hypothesis
                    'left-value 'right-value))
              'right))
            'left))))
       'upper))}))

(def index-weaken-injective-spec
  {:name 'finite/index-weaken-injective
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['left (index-of 'upper)]
     ['right (index-of 'upper)]
     ['same
      (index-equality
       (app succ 'upper)
       (weaken-index 'upper 'left)
       (weaken-index 'upper 'right))]]
    (index-equality 'upper 'left 'right))
   :value
   (function/lam
    [['upper nat]
     ['left (index-of 'upper)]
     ['right (index-of 'upper)]
     ['same
      (index-equality
       (app succ 'upper)
       (weaken-index 'upper 'left)
       (weaken-index 'upper 'right))]]
    (let [prior (index-of 'upper)
          current (index-of (app succ 'upper))
          recover
          (function/lam
           [['candidate current]]
           (option-eliminate
            prior prior 'left
            (function/lam [['value prior]] 'value)
            'candidate))]
      (app
       (function/const* 'equality/congruent-function
                        [type-level type-level])
       current prior recover
       (weaken-index 'upper 'left)
       (weaken-index 'upper 'right)
       'same)))})

(def index-decide-equality-reflexive-true-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (function/forall
          [['value (index-of 'upper)]]
          (bool-equality
           (decide-index-equality 'upper 'value 'value)
           true-value)))]
    {:name 'finite/index-decide-equality-reflexive-true
     :universes []
     :type
     (function/forall
      [['upper nat] ['value (index-of 'upper)]]
      (bool-equality
       (decide-index-equality 'upper 'value 'value)
       true-value))
     :value
     (function/lam
      [['upper nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (let [empty (index-of (function/const* 'data/zero []))]
         (function/lam
          [['value empty]]
          (app
           (function/const* 'finite/Empty.rec [zero-level])
           (function/lam
            [['candidate empty]]
            (bool-equality
             (decide-index-equality
              (function/const* 'data/zero [])
              'candidate 'candidate)
             true-value))
           (function/lam
            [['previous empty]
             ['induction-hypothesis
              (bool-equality
               (decide-index-equality
                (function/const* 'data/zero [])
                'previous 'previous)
               true-value)]]
            'induction-hypothesis)
           'value)))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (app motive 'previous)]]
        (let [prior (index-of 'previous)
              current (index-of (app succ 'previous))
              option-motive
              (function/lam
               [['value current]]
               (bool-equality
                (decide-index-equality
                 (app succ 'previous) 'value 'value)
                true-value))]
          (function/lam
           [['value current]]
           (app
            (function/const* 'data/Option.rec [type-level zero-level])
            prior option-motive
            (app
             (function/const* 'equality/reflexive [type-level])
             bool true-value)
            (function/lam
             [['prior-value prior]]
             (app 'induction-hypothesis 'prior-value))
            'value))))
       'upper))}))

(def index-equality-implies-decide-equality-true-spec
  {:name 'finite/index-equality-implies-decide-equality-true
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['left (index-of 'upper)]
     ['right (index-of 'upper)]
     ['same (index-equality 'upper 'left 'right)]]
    (bool-equality
     (decide-index-equality 'upper 'left 'right)
     true-value))
   :value
   (function/lam
    [['upper nat]
     ['left (index-of 'upper)]
     ['right (index-of 'upper)]
     ['same (index-equality 'upper 'left 'right)]]
    (app
     (function/const* 'equality/substitution [type-level])
     (index-of 'upper) 'left 'right 'same
     (function/lam
      [['current-right (index-of 'upper)]]
      (bool-equality
       (decide-index-equality 'upper 'left 'current-right)
       true-value))
     (app
      (function/const*
       'finite/index-decide-equality-reflexive-true [])
      'upper 'left)))})

(def index-decide-equality-true-sound-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (function/forall
          [['left (index-of 'upper)]
           ['right (index-of 'upper)]
           ['accepted
            (bool-equality
             (decide-index-equality 'upper 'left 'right)
             true-value)]]
          (index-equality 'upper 'left 'right)))]
    {:name 'finite/index-decide-equality-true-sound
     :universes []
     :type
     (function/forall
      [['upper nat]
       ['left (index-of 'upper)]
       ['right (index-of 'upper)]
       ['accepted
        (bool-equality
         (decide-index-equality 'upper 'left 'right)
         true-value)]]
      (index-equality 'upper 'left 'right))
     :value
     (function/lam
      [['upper nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (let [empty (index-of (function/const* 'data/zero []))]
         (function/lam
          [['left empty]]
          (let [result
                (function/forall
                 [['right empty]
                  ['accepted
                   (bool-equality
                    (decide-index-equality
                     (function/const* 'data/zero [])
                     'left 'right)
                    true-value)]]
                 (index-equality
                  (function/const* 'data/zero []) 'left 'right))
                empty-motive
                (function/lam [['ignored empty]] result)]
            (app
             (function/const* 'finite/Empty.rec [zero-level])
             empty-motive
             (function/lam
              [['previous empty]
               ['induction-hypothesis result]]
              'induction-hypothesis)
             'left))))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (app motive 'previous)]]
        (let [prior (index-of 'previous)
              current (index-of (app succ 'previous))
              none (last-index 'previous)
              some (fn [value] (weaken-index 'previous value))
              outer-motive
              (function/lam
               [['left current]]
               (function/forall
                [['right current]
                 ['accepted
                  (bool-equality
                   (decide-index-equality
                    (app succ 'previous) 'left 'right)
                   true-value)]]
                (index-equality
                 (app succ 'previous) 'left 'right)))]
          (function/lam
           [['left current]]
           (app
            (function/const* 'data/Option.rec [type-level zero-level])
            prior outer-motive
            (let [right-motive
                  (function/lam
                   [['right current]]
                   (function/arrow
                    (bool-equality
                     (decide-index-equality
                      (app succ 'previous) none 'right)
                     true-value)
                    (index-equality
                     (app succ 'previous) none 'right)))]
              (function/lam
               [['right current]]
               (app
                (function/const* 'data/Option.rec
                                 [type-level zero-level])
                prior right-motive
                (function/lam
                 [['ignored-accepted
                   (bool-equality true-value true-value)]]
                 (app
                  (function/const* 'equality/reflexive [type-level])
                  current none))
                (function/lam
                 [['right-value prior]
                  ['accepted
                   (bool-equality false-value true-value)]]
                 (app
                  (function/const* 'proposition/explode [])
                  (index-equality
                   (app succ 'previous) none (some 'right-value))
                  (false-not-true 'accepted)))
                'right)))
            (function/lam
             [['left-value prior]]
             (let [left-some (some 'left-value)
                   right-motive
                   (function/lam
                    [['right current]]
                    (function/arrow
                     (bool-equality
                      (decide-index-equality
                       (app succ 'previous) left-some 'right)
                      true-value)
                     (index-equality
                      (app succ 'previous) left-some 'right)))]
               (function/lam
                [['right current]]
                (app
                 (function/const* 'data/Option.rec
                                  [type-level zero-level])
                 prior right-motive
                 (function/lam
                  [['accepted
                    (bool-equality false-value true-value)]]
                  (app
                   (function/const* 'proposition/explode [])
                   (index-equality
                    (app succ 'previous) left-some none)
                   (false-not-true 'accepted)))
                 (function/lam
                  [['right-value prior]
                   ['accepted
                    (bool-equality
                     (decide-index-equality
                      'previous 'left-value 'right-value)
                     true-value)]]
                  (app
                   (function/const* 'equality/congruent-function
                                    [type-level type-level])
                   prior current
                   (function/lam
                    [['value prior]] (some 'value))
                   'left-value 'right-value
                   (app 'induction-hypothesis
                        'left-value 'right-value 'accepted)))
                 'right))))
            'left))))
       'upper))}))

(def index-last-different-from-weaken-spec
  {:name 'finite/index-last-different-from-weaken
   :universes []
   :type
   (function/forall
    [['upper nat] ['source (index-of 'upper)]]
    (proposition/negation
     (index-equality
      (app succ 'upper)
      (last-index 'upper)
      (weaken-index 'upper 'source))))
   :value
   (function/lam
    [['upper nat] ['source (index-of 'upper)]
     ['same
      (index-equality
       (app succ 'upper)
       (last-index 'upper)
       (weaken-index 'upper 'source))]]
    (let [prior (index-of 'upper)
          current (index-of (app succ 'upper))
          separates
          (function/lam
           [['candidate current]]
           (app
            (function/const* 'data/Option.rec [type-level type-level])
            prior
            (function/lam [['ignored current]] 'Prop)
            (proposition/truth)
            (function/lam [['ignored prior]] (proposition/falsity))
            'candidate))]
      (app 'same separates
           (function/const* 'proposition/trivial []))))})

(def index-weaken-membership-reflects-spec
  (let [prior (index-of 'upper)
        current (index-of (app succ 'upper))
        prior-list (list-of prior)
        weaken
        (function/lam
         [['source prior]] (weaken-index 'upper 'source))
        mapped
        (fn [items] (map-list prior current weaken items))
        motive
        (function/lam
         [['items prior-list]]
         (function/forall
          [['selected prior]
           ['mapped-member
            (membership current (mapped 'items)
                        (weaken-index 'upper 'selected))]]
          (membership prior 'items 'selected)))]
    {:name 'finite/index-weaken-membership-reflects
     :universes []
     :type
     (function/forall
      [['upper nat]
       ['items prior-list]
       ['selected prior]
       ['mapped-member
        (membership current (mapped 'items)
                    (weaken-index 'upper 'selected))]]
      (membership prior 'items 'selected))
     :value
     (function/lam
      [['upper nat] ['items prior-list]]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       prior motive
       (function/lam
        [['selected prior]
         ['impossible
          (membership current (mapped (nil-list prior))
                      (weaken-index 'upper 'selected))]]
        (app (function/const* 'proposition/explode [])
             (membership prior (nil-list prior) 'selected)
             'impossible))
       (function/lam
        [['head prior] ['tail prior-list]
         ['induction-hypothesis (app motive 'tail)]
         ['selected prior]
         ['mapped-member
          (membership
           current
           (mapped (cons-list prior 'head 'tail))
           (weaken-index 'upper 'selected))]]
        (let [at-head
              (index-equality
               (app succ 'upper)
               (weaken-index 'upper 'selected)
               (weaken-index 'upper 'head))
              in-tail
              (membership current (mapped 'tail)
                          (weaken-index 'upper 'selected))
              source-head (index-equality 'upper 'selected 'head)
              source-tail (membership prior 'tail 'selected)]
          (app
           (function/const* 'proposition/use-disjunction [])
           at-head in-tail
           (membership prior (cons-list prior 'head 'tail) 'selected)
           'mapped-member
           (function/lam
            [['same at-head]]
            (app
             (function/const* 'proposition/left-disjunct [])
             source-head source-tail
             (app
              (function/const* 'finite/index-weaken-injective [])
              'upper 'selected 'head 'same)))
           (function/lam
            [['tail-member in-tail]]
            (app
             (function/const* 'proposition/right-disjunct [])
             source-head source-tail
             (app 'induction-hypothesis 'selected 'tail-member))))))
       'items))}))

(def index-last-not-member-map-weaken-spec
  (let [prior (index-of 'upper)
        current (index-of (app succ 'upper))
        prior-list (list-of prior)
        weaken
        (function/lam
         [['source prior]] (weaken-index 'upper 'source))
        mapped
        (fn [items] (map-list prior current weaken items))
        motive
        (function/lam
         [['items prior-list]]
         (proposition/negation
          (membership current (mapped 'items) (last-index 'upper))))]
    {:name 'finite/index-last-not-member-map-weaken
     :universes []
     :type
     (function/forall
      [['upper nat] ['items prior-list]]
      (proposition/negation
       (membership current (mapped 'items) (last-index 'upper))))
     :value
     (function/lam
      [['upper nat] ['items prior-list]]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       prior motive
       (function/lam
        [['impossible
          (membership current (mapped (nil-list prior))
                      (last-index 'upper))]]
        'impossible)
       (function/lam
        [['head prior] ['tail prior-list]
         ['induction-hypothesis (app motive 'tail)]
         ['member
          (membership current
                      (mapped (cons-list prior 'head 'tail))
                      (last-index 'upper))]]
        (let [at-head
              (index-equality
               (app succ 'upper)
               (last-index 'upper)
               (weaken-index 'upper 'head))
              in-tail
              (membership current (mapped 'tail) (last-index 'upper))]
          (app
           (function/const* 'proposition/use-disjunction [])
           at-head in-tail (proposition/falsity) 'member
           (function/lam
            [['same at-head]]
            (app
             (function/const* 'finite/index-last-different-from-weaken [])
             'upper 'head 'same))
           (function/lam
            [['tail-member in-tail]]
            (app 'induction-hypothesis 'tail-member)))))
       'items))}))

(def index-map-weaken-no-duplicates-spec
  (let [prior (index-of 'upper)
        current (index-of (app succ 'upper))
        prior-list (list-of prior)
        weaken
        (function/lam
         [['source prior]] (weaken-index 'upper 'source))
        mapped
        (fn [items] (map-list prior current weaken items))
        motive
        (function/lam
         [['items prior-list]]
         (function/arrow
          (no-duplicates prior 'items)
          (no-duplicates current (mapped 'items))))]
    {:name 'finite/index-map-weaken-no-duplicates
     :universes []
     :type
     (function/forall
      [['upper nat] ['items prior-list]
       ['distinct (no-duplicates prior 'items)]]
      (no-duplicates current (mapped 'items)))
     :value
     (function/lam
      [['upper nat] ['items prior-list]]
      (app
       (function/const* 'data/List.rec [type-level zero-level])
       prior motive
       (function/lam
        [['ignored-distinct (no-duplicates prior (nil-list prior))]]
        (function/const* 'proposition/trivial []))
       (function/lam
        [['head prior] ['tail prior-list]
         ['induction-hypothesis (app motive 'tail)]
         ['distinct
          (no-duplicates prior (cons-list prior 'head 'tail))]]
        (let [source-head-absent
              (app
               (function/const* 'proposition/left [])
               (proposition/negation (membership prior 'tail 'head))
               (no-duplicates prior 'tail) 'distinct)
              source-tail-distinct
              (app
               (function/const* 'proposition/right [])
               (proposition/negation (membership prior 'tail 'head))
               (no-duplicates prior 'tail) 'distinct)
              target-head-absent
              (function/lam
               [['mapped-member
                 (membership current (mapped 'tail)
                             (weaken-index 'upper 'head))]]
               (app
                source-head-absent
                (app
                 (function/const*
                  'finite/index-weaken-membership-reflects [])
                 'upper 'tail 'head 'mapped-member)))
              target-tail-distinct
              (app 'induction-hypothesis source-tail-distinct)]
          (app
           (function/const* 'proposition/conjoin [])
           (proposition/negation
            (membership current (mapped 'tail)
                        (weaken-index 'upper 'head)))
           (no-duplicates current (mapped 'tail))
           target-head-absent target-tail-distinct)))
       'items))}))

(def index-enumeration-no-duplicates-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (no-duplicates (index-of 'upper) (index-enumeration 'upper)))]
    {:name 'finite/index-enumeration-no-duplicates
     :universes []
     :type
     (function/forall
      [['upper nat]]
      (no-duplicates (index-of 'upper) (index-enumeration 'upper)))
     :value
     (function/lam
      [['upper nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/const* 'proposition/trivial [])
       (function/lam
        [['previous nat]
         ['induction-hypothesis (app motive 'previous)]]
        (let [prior (index-of 'previous)
              current (index-of (app succ 'previous))
              items (index-enumeration 'previous)
              weaken
              (function/lam
               [['source prior]] (weaken-index 'previous 'source))
              mapped (map-list prior current weaken items)
              last-absent
              (app
               (function/const*
                'finite/index-last-not-member-map-weaken [])
               'previous items)
              mapped-distinct
              (app
               (function/const*
                'finite/index-map-weaken-no-duplicates [])
               'previous items 'induction-hypothesis)]
          (app
           (function/const* 'proposition/conjoin [])
           (proposition/negation
            (membership current mapped (last-index 'previous)))
           (no-duplicates current mapped)
           last-absent mapped-distinct)))
       'upper))}))

(def index-finset-spec
  {:name 'finite/index-finset
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/forall
    [['upper nat]] (finset-of (index-of 'upper)))
   :value
   (function/lam
    [['upper nat]]
    (let [element (index-of 'upper)
          items (index-enumeration 'upper)]
      (app
       (function/const* 'data/subtype [type-level])
       (list-of element)
       (function/lam
        [['candidate (list-of element)]]
        (no-duplicates element 'candidate))
       items
       (app
        (function/const* 'finite/index-enumeration-no-duplicates [])
        'upper))))})

(def index-certified-equality-spec
  {:name 'finite/certified-index-equality
   :universes []
   :type
   (function/forall
    [['upper nat]]
    (let [element (index-of 'upper)
          decision
          (function/lam
           [['left element] ['right element]]
           (decide-index-equality 'upper 'left 'right))]
      (certified-equality element decision)))
   :value
   (function/lam
    [['upper nat]]
    (let [element (index-of 'upper)
          decision
          (function/lam
           [['left element] ['right element]]
           (decide-index-equality 'upper 'left 'right))
          sound (equality-soundness element decision)
          complete (equality-completeness element decision)]
      (app
       (function/const* 'proposition/conjoin [])
       sound complete
       (function/lam
        [['left element] ['right element]
         ['accepted
          (bool-equality
           (decide-index-equality 'upper 'left 'right)
           true-value)]]
        (app
         (function/const* 'finite/index-decide-equality-true-sound [])
         'upper 'left 'right 'accepted))
       (function/lam
        [['left element] ['right element]
         ['same (index-equality 'upper 'left 'right)]]
        (app
         (function/const*
          'finite/index-equality-implies-decide-equality-true [])
         'upper 'left 'right 'same)))))})

(def index-exhaustive-carrier-spec
  {:name 'finite/index-exhaustive-carrier
   :universes []
   :type
   (function/forall
    [['upper nat]]
    (let [element (index-of 'upper)
          states (app (function/const* 'finite/index-finset []) 'upper)
          decision
          (function/lam
           [['left element] ['right element]]
           (decide-index-equality 'upper 'left 'right))]
      (exhaustive-carrier element states decision)))
   :value
   (function/lam
    [['upper nat]]
    (let [element (index-of 'upper)
          states (app (function/const* 'finite/index-finset []) 'upper)
          decision
          (function/lam
           [['left element] ['right element]]
           (decide-index-equality 'upper 'left 'right))
          certified (certified-equality element decision)
          covered
          (function/forall
           [['state element]]
           (membership element
                       (finset-enumeration element states)
                       'state))]
      (app
       (function/const* 'proposition/conjoin [])
       certified covered
       (app
        (function/const* 'finite/certified-index-equality []) 'upper)
       (function/lam
        [['state element]]
        (app
         (function/const* 'finite/index-enumeration-covers [])
         'upper 'state)))))})

(def index-successor-cases-spec
  (let [upper-successor (app succ 'upper)
        source-type (index-of upper-successor)
        is-last
        (fn [candidate]
          (index-equality upper-successor candidate (last-index 'upper)))
        is-weakened
        (fn [candidate]
          (proposition/existence
           type-level (index-of 'upper)
           (function/lam
            [['prior (index-of 'upper)]]
            (index-equality
             upper-successor candidate (weaken-index 'upper 'prior)))))
        result
        (fn [candidate]
          (proposition/disjunction
           (is-last candidate) (is-weakened candidate)))
        motive (function/lam [['candidate source-type]] (result 'candidate))]
    {:name 'finite/index-successor-cases
     :universes []
     :type
     (function/forall
      [['upper nat] ['source source-type]] (result 'source))
     :value
     (function/lam
      [['upper nat] ['source source-type]]
      (app
       (function/const* 'data/Option.rec [type-level zero-level])
       (index-of 'upper)
       motive
       (app
        (function/const* 'proposition/left-disjunct [])
        (is-last (last-index 'upper))
        (is-weakened (last-index 'upper))
        (app (function/const* 'equality/reflexive [type-level])
             source-type (last-index 'upper)))
       (function/lam
        [['previous (index-of 'upper)]]
        (app
         (function/const* 'proposition/right-disjunct [])
         (is-last (weaken-index 'upper 'previous))
         (is-weakened (weaken-index 'upper 'previous))
         (app
          (function/const* 'proposition/witness [type-level])
          (index-of 'upper)
          (function/lam
           [['candidate (index-of 'upper)]]
           (index-equality
            upper-successor
            (weaken-index 'upper 'previous)
            (weaken-index 'upper 'candidate)))
          'previous
          (app (function/const* 'equality/reflexive [type-level])
               source-type (weaken-index 'upper 'previous)))))
       'source))}))

(def index-enumeration-covers-spec
  (let [claim
        (fn [bound source]
          (membership (index-of bound) (index-enumeration bound) source))
        motive
        (function/lam
         [['bound nat]]
         (function/forall
          [['source (index-of 'bound)]] (claim 'bound 'source)))]
    {:name 'finite/index-enumeration-covers
     :universes []
     :type
     (function/forall
      [['upper nat] ['source (index-of 'upper)]]
      (claim 'upper 'source))
     :value
     (function/lam
      [['upper nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['source (index-of (function/const* 'data/zero []))]]
        (app
         (function/const* 'finite/Empty.rec [zero-level])
         (function/lam
          [['candidate (function/const* 'finite/Empty [])]]
          (claim (function/const* 'data/zero []) 'candidate))
         (function/lam
          [['previous (function/const* 'finite/Empty [])]
           ['induction-hypothesis
            (claim (function/const* 'data/zero []) 'previous)]]
          'induction-hypothesis)
         'source))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (app motive 'previous)]
         ['source (index-of (app succ 'previous))]]
        (let [prior (index-of 'previous)
              current (index-of (app succ 'previous))
              weaken
              (function/lam
               [['candidate prior]] (weaken-index 'previous 'candidate))
              tail (map-list prior current weaken
                             (index-enumeration 'previous))
              result (membership current (index-enumeration (app succ 'previous))
                                 'source)
              option-motive
              (function/lam
               [['candidate current]]
               (membership current
                           (index-enumeration (app succ 'previous))
                           'candidate))]
          (app
           (function/const* 'data/Option.rec [type-level zero-level])
           prior option-motive
           (app
            (function/const* 'proposition/left-disjunct [])
            (index-equality (app succ 'previous)
                            (last-index 'previous) (last-index 'previous))
            (membership current tail (last-index 'previous))
            (app (function/const* 'equality/reflexive [type-level])
                 current (last-index 'previous)))
           (function/lam
            [['prior-source prior]]
            (let [weakened (weaken-index 'previous 'prior-source)
                  mapped-member
                  (app
                   (function/const* 'list/membership-map
                                    [zero-level zero-level])
                   prior current weaken
                   (index-enumeration 'previous) 'prior-source
                   (app 'induction-hypothesis 'prior-source))]
              (app
               (function/const* 'proposition/right-disjunct [])
               (index-equality (app succ 'previous)
                               weakened (last-index 'previous))
               (membership current tail weakened)
               mapped-member)))
           'source)))
       'upper))}))

(def foundation-definition-specs
  [index-spec index-last-spec index-weaken-spec index-enumeration-spec
   index-decide-equality-spec])
(def definition-specs
  (conj foundation-definition-specs index-finset-spec))
(def pre-finset-theorem-specs
  [index-weaken-injective-spec
   index-decide-equality-reflexive-true-spec
   index-equality-implies-decide-equality-true-spec
   index-decide-equality-true-sound-spec
   index-last-different-from-weaken-spec
   index-weaken-membership-reflects-spec
   index-last-not-member-map-weaken-spec
   index-map-weaken-no-duplicates-spec
   index-enumeration-no-duplicates-spec
   index-successor-cases-spec
   index-enumeration-covers-spec
   index-certified-equality-spec])
(def post-finset-theorem-specs [index-exhaustive-carrier-spec])
(def theorem-specs
  (concat pre-finset-theorem-specs post-finset-theorem-specs))
(def declaration-specs
  (concat foundation-definition-specs
          pre-finset-theorem-specs
          [index-finset-spec]
          post-finset-theorem-specs))

(defn- extend-spec-if-missing [env alias spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env :finite-index-support [spec])))

(defn extend-environment [env]
  (let [env
        (-> env
            (extend-spec-if-missing
             'finite/certified-equality-decision
             diagonal-spike/certified-equality-decision-spec)
            (extend-spec-if-missing
             'finite/certified-exhaustive-carrier
             diagonal-spike/certified-exhaustive-carrier-spec))
        empty-id (environment/resolve-id env 'finite/Empty)
        installed?
        (every? #(environment/resolve-id env (:name %))
                declaration-specs)]
    (cond
      (and empty-id installed?) env
      (or empty-id installed?)
      (throw
       (ex-info "Finite index package is partially installed"
                {:empty-installed? (boolean empty-id)
                 :declarations-installed? installed?}))
      :else
      (let [added (kernel/add-inductive-block env empty-block-spec)]
        (when-not (= :accepted (:status added))
          (throw (ex-info "Finite Empty inductive block rejected"
                          {:result added})))
        (support/extend-with
         (:environment added) :finite-index
         declaration-specs)))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
(defn block-id [env] (environment/resolve-id env 'finite/Empty))
