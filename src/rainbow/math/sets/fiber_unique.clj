(ns rainbow.math.sets.fiber-unique
  "Unique existence from subsingleton predicates, applied to bijection fibers."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sets.fiber-characterization :as characterization]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- predicate-subsingleton [predicate]
  (function/forall
   [['left 'A :implicit] ['left-evidence (function/app predicate 'left)]
    ['right 'A :implicit] ['right-evidence (function/app predicate 'right)]]
   (function/equality data-level 'A 'left 'right)))

(defn- fiber-within [mapping source target]
  (function/app (function/const* 'set/fiber-within [U V])
                'A 'B mapping source target))

(def unique-existence-of-existence-and-subsingleton-spec
  (let [exists (proposition/existence data-level 'A 'predicate)
        subsingleton (predicate-subsingleton 'predicate)
        unique (proposition/unique-existence data-level 'A 'predicate)]
    {:name 'proposition/unique-existence-of-existence-and-subsingleton
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['some-evidence exists] ['subsingleton-evidence subsingleton]]
      unique)
     :value
     (function/lam
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['some-evidence exists] ['subsingleton-evidence subsingleton]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A 'predicate unique 'some-evidence
       (function/lam
        [['selected 'A]
         ['selected-evidence (function/app 'predicate 'selected)]]
        (function/app
         (function/const* 'proposition/unique-witness [data-level])
         'A 'predicate 'selected 'selected-evidence
         (function/lam
          [['other 'A]
           ['other-evidence (function/app 'predicate 'other)]]
          (function/app 'subsingleton-evidence
                        'other 'other-evidence
                        'selected 'selected-evidence))))))}))

(def existence-and-subsingleton-of-unique-existence-spec
  (let [exists (proposition/existence data-level 'A 'predicate)
        subsingleton (predicate-subsingleton 'predicate)
        unique (proposition/unique-existence data-level 'A 'predicate)
        result (proposition/conjunction exists subsingleton)]
    {:name 'proposition/existence-and-subsingleton-of-unique-existence
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['unique-evidence unique]]
      result)
     :value
     (function/lam
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['unique-evidence unique]]
      (function/app
       (function/const* 'proposition/use-unique-witness [data-level])
       'A 'predicate result 'unique-evidence
       (function/lam
        [['selected 'A]
         ['selected-evidence (function/app 'predicate 'selected)]
         ['selected-unique
          (proposition/uniqueness data-level 'A 'predicate 'selected)]]
        (function/app
         (function/const* 'proposition/conjoin [])
         exists subsingleton
         (function/app
          (function/const* 'proposition/witness [data-level])
          'A 'predicate 'selected 'selected-evidence)
         (function/lam
          [['left 'A :implicit]
           ['left-evidence (function/app 'predicate 'left)]
           ['right 'A :implicit]
           ['right-evidence (function/app 'predicate 'right)]]
          (function/app
           (function/const* 'equality/transitive [data-level])
           'A 'left 'selected 'right
           (function/app 'selected-unique 'left 'left-evidence)
           (function/app
            (function/const* 'equality/symmetric [data-level])
            'A 'right 'selected
            (function/app 'selected-unique
                          'right 'right-evidence))))))))}))

(def unique-existence-equivalent-existence-and-subsingleton-spec
  (let [exists (proposition/existence data-level 'A 'predicate)
        subsingleton (predicate-subsingleton 'predicate)
        both (proposition/conjunction exists subsingleton)
        unique (proposition/unique-existence data-level 'A 'predicate)]
    {:name 'proposition/unique-existence-equivalent-existence-and-subsingleton
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]]
      (proposition/equivalence unique both))
     :value
     (function/lam
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       unique both
       (function/app
        (function/const*
         'proposition/existence-and-subsingleton-of-unique-existence [U])
        'A 'predicate)
       (function/lam
        [['both-evidence both]]
        (function/app
         (function/const*
          'proposition/unique-existence-of-existence-and-subsingleton [U])
         'A 'predicate
         (function/app (function/const* 'proposition/left [])
                       exists subsingleton 'both-evidence)
         (function/app (function/const* 'proposition/right [])
                       exists subsingleton 'both-evidence)))))}))

(def bijective-on-has-unique-fibers-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        maps
        (function/app (function/const* 'set/maps-to [U V])
                      'A 'B 'mapping 'source 'target)
        injection
        (function/app (function/const* 'set/injective-on [U V])
                      'A 'B 'mapping 'source)
        surjection
        (function/app (function/const* 'set/surjective-on [U V])
                      'A 'B 'mapping 'source 'target)
        bijection
        (function/app (function/const* 'set/bijective-on [U V])
                      'A 'B 'mapping 'source 'target)
        nonempty-fibers
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (function/app (function/const* 'set/nonempty [U])
                       'A (fiber-within 'mapping 'source 'value)))
        subsingleton-fibers
        (function/forall
         [['value 'B]]
         (function/app (function/const* 'set/subsingleton [U])
                       'A (fiber-within 'mapping 'source 'value)))
        unique-fibers
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (proposition/unique-existence
          data-level 'A (fiber-within 'mapping 'source 'value)))]
    {:name 'set/bijective-on-has-unique-fibers
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['bijection-evidence bijection]]
      unique-fibers)
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]
       ['bijection-evidence bijection]]
      (let [injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             maps (proposition/conjunction injection surjection)
             'bijection-evidence)
            injection-evidence
            (function/app
             (function/const* 'proposition/left [])
             injection surjection injective-surjective)
            surjection-evidence
            (function/app
             (function/const* 'proposition/right [])
             injection surjection injective-surjective)
            all-nonempty
            (function/app
             (function/const* 'proposition/equivalence-forward [])
             surjection nonempty-fibers
             (function/app
              (function/const*
               'set/surjective-on-equivalent-nonempty-fibers [U V])
              'A 'B 'mapping 'source 'target)
             surjection-evidence)
            all-subsingleton
            (function/app
             (function/const* 'proposition/equivalence-forward [])
             injection subsingleton-fibers
             (function/app
              (function/const*
               'set/injective-on-equivalent-subsingleton-fibers [U V])
              'A 'B 'mapping 'source)
             injection-evidence)]
        (function/lam
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (function/app
          (function/const*
           'proposition/unique-existence-of-existence-and-subsingleton [U])
          'A (fiber-within 'mapping 'source 'value)
          (function/app all-nonempty 'value 'target-member)
          (function/app all-subsingleton 'value)))))}))

(def bijective-on-equivalent-maps-to-and-unique-fibers-spec
  (let [set-a (set-of U 'A)
        set-b (set-of V 'B)
        maps
        (function/app (function/const* 'set/maps-to [U V])
                      'A 'B 'mapping 'source 'target)
        injection
        (function/app (function/const* 'set/injective-on [U V])
                      'A 'B 'mapping 'source)
        surjection
        (function/app (function/const* 'set/surjective-on [U V])
                      'A 'B 'mapping 'source 'target)
        bijection
        (function/app (function/const* 'set/bijective-on [U V])
                      'A 'B 'mapping 'source 'target)
        unique-fibers
        (function/forall
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value)]]
         (proposition/unique-existence
          data-level 'A (fiber-within 'mapping 'source 'value)))
        maps-and-unique (proposition/conjunction maps unique-fibers)]
    {:name 'set/bijective-on-equivalent-maps-to-and-unique-fibers
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]]
      (proposition/equivalence bijection maps-and-unique))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['source set-a] ['target set-b]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       bijection maps-and-unique
       (function/lam
        [['bijection-evidence bijection]]
        (function/app
         (function/const* 'proposition/conjoin [])
         maps unique-fibers
         (function/app
          (function/const* 'proposition/left [])
          maps (proposition/conjunction injection surjection)
          'bijection-evidence)
         (function/app
          (function/const* 'set/bijective-on-has-unique-fibers [U V])
          'A 'B 'mapping 'source 'target 'bijection-evidence)))
       (function/lam
        [['maps-and-unique-evidence maps-and-unique]]
        (let [maps-evidence
              (function/app
               (function/const* 'proposition/left [])
               maps unique-fibers 'maps-and-unique-evidence)
              unique-fibers-evidence
              (function/app
               (function/const* 'proposition/right [])
               maps unique-fibers 'maps-and-unique-evidence)
              injection-evidence
              (function/lam
               [['left 'A :implicit]
                ['left-member (function/app 'source 'left)]
                ['right 'A :implicit]
                ['right-member (function/app 'source 'right)]
                ['same-image
                 (function/equality
                  target-data-level 'B
                  (function/app 'mapping 'left)
                  (function/app 'mapping 'right))]]
               (let [fiber-target (function/app 'mapping 'left)
                     fiber-set
                     (fiber-within 'mapping 'source fiber-target)
                     same-right-left
                     (function/app
                      (function/const* 'equality/symmetric
                                       [target-data-level])
                      'B (function/app 'mapping 'left)
                      (function/app 'mapping 'right) 'same-image)]
                 (function/app
                  (function/const* 'proposition/use-unique-witness
                                   [data-level])
                  'A fiber-set
                  (function/equality data-level 'A 'left 'right)
                  (function/app
                   unique-fibers-evidence fiber-target
                   (function/app maps-evidence 'left 'left-member))
                  (function/lam
                   [['selected 'A]
                    ['selected-fiber (function/app fiber-set 'selected)]
                    ['selected-unique
                     (proposition/uniqueness
                      data-level 'A fiber-set 'selected)]]
                   (let [left-fiber
                         (function/app
                          (function/const* 'proposition/conjoin [])
                          (function/app 'source 'left)
                          (function/equality
                           target-data-level 'B
                           (function/app 'mapping 'left) fiber-target)
                          'left-member
                          (function/app
                           (function/const* 'equality/reflexive
                                            [target-data-level])
                           'B fiber-target))
                         right-fiber
                         (function/app
                          (function/const* 'proposition/conjoin [])
                          (function/app 'source 'right)
                          (function/equality
                           target-data-level 'B
                           (function/app 'mapping 'right) fiber-target)
                          'right-member same-right-left)]
                     (function/app
                      (function/const* 'equality/transitive [data-level])
                      'A 'left 'selected 'right
                      (function/app 'selected-unique
                                    'left left-fiber)
                      (function/app
                       (function/const* 'equality/symmetric [data-level])
                       'A 'right 'selected
                       (function/app 'selected-unique
                                     'right right-fiber))))))))
              surjection-evidence
              (function/lam
               [['value 'B :implicit]
                ['target-member (function/app 'target 'value)]]
               (let [fiber-set (fiber-within 'mapping 'source 'value)
                     exists-fiber
                     (proposition/existence data-level 'A fiber-set)]
                 (function/app
                  (function/const* 'proposition/use-unique-witness
                                   [data-level])
                  'A fiber-set exists-fiber
                  (function/app unique-fibers-evidence
                                'value 'target-member)
                  (function/lam
                   [['selected 'A]
                    ['selected-fiber (function/app fiber-set 'selected)]
                    ['selected-unique
                     (proposition/uniqueness
                      data-level 'A fiber-set 'selected)]]
                   (function/app
                    (function/const* 'proposition/witness [data-level])
                    'A fiber-set 'selected 'selected-fiber)))))]
          (function/app
           (function/const* 'proposition/conjoin [])
           maps (proposition/conjunction injection surjection)
           maps-evidence
           (function/app
            (function/const* 'proposition/conjoin [])
            injection surjection
            injection-evidence surjection-evidence))))))}))

(def theorem-specs
  [unique-existence-of-existence-and-subsingleton-spec
   existence-and-subsingleton-of-unique-existence-spec
   unique-existence-equivalent-existence-and-subsingleton-spec
   bijective-on-has-unique-fibers-spec
   bijective-on-equivalent-maps-to-and-unique-fibers-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      characterization/extend-environment
      (support/extend-with :set-fiber-unique theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
