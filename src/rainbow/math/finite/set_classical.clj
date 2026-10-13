(ns rainbow.math.finite.set-classical
  "Classical finite-set transport, kept separate from the axiom-free layer."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U finite-set/U)
(def V finite-set/V)
(def data-level finite-set/data-level)
(def target-data-level finite-set/target-data-level)
(def type-u finite-set/type-u)
(def type-v finite-set/type-v)

(defn image-cover [element enumeration mapping source]
  (function/forall
   [['value element]
    ['member (function/app source 'value)]]
   (finite-set/target-membership
    'B enumeration (function/app mapping 'value))))

(def finite-injective-enumeration-spec
  (let [set-a (finite-set/set-of 'A)
        list-a (finite-set/list-of 'A)
        list-b (finite-set/target-list-of 'B)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        nil-b (function/app (function/const* 'data/nil [target-data-level])
                            'B)
        motive
        (function/lam
         [['enumeration list-b]]
         (function/forall
          [['source set-a]
           ['injection
            (finite-set/injective-on 'A 'B 'mapping 'source)]
           ['source-image-cover
            (image-cover 'A 'enumeration 'mapping 'source)]]
          (finite-set/finite 'A 'source)))
        nil-case
        (function/lam
         [['source set-a]
          ['injection
           (finite-set/injective-on 'A 'B 'mapping 'source)]
          ['source-image-cover (image-cover 'A nil-b 'mapping 'source)]]
         (function/app
          (function/const* 'proposition/witness [data-level])
          list-a
          (function/lam
           [['enumeration list-a]]
           (finite-set/cover 'A 'source 'enumeration))
          nil-a
          (function/lam
           [['value 'A] ['member (function/app 'source 'value)]]
           (function/app
            (function/const* 'proposition/explode [])
            (finite-set/membership 'A nil-a 'value)
            (function/app 'source-image-cover 'value 'member)))))
        cons-case
        (function/lam
         [['head 'B] ['tail list-b]
          ['induction-hypothesis
           (function/forall
            [['source set-a]
             ['injection
              (finite-set/injective-on 'A 'B 'mapping 'source)]
             ['source-image-cover
              (image-cover 'A 'tail 'mapping 'source)]]
            (finite-set/finite 'A 'source))]
          ['source set-a]
          ['injection
           (finite-set/injective-on 'A 'B 'mapping 'source)]
          ['source-image-cover
           (image-cover
            'A
            (function/app (function/const* 'data/cons [target-data-level])
                          'B 'head 'tail)
            'mapping 'source)]]
         (let [witness-predicate
               (function/lam
                [['candidate 'A]]
                (proposition/conjunction
                 (function/app 'source 'candidate)
                 (finite-set/target-equality
                  'B (function/app 'mapping 'candidate) 'head)))
               witness-exists
               (proposition/existence data-level 'A witness-predicate)
               target (finite-set/finite 'A 'source)]
           (function/app
            (function/const* 'logic/classical-cases [])
            witness-exists target
            (function/lam
             [['some-witness witness-exists]]
             (function/app
              (function/const* 'proposition/use-witness [data-level])
              'A witness-predicate target 'some-witness
              (function/lam
               [['representative 'A]
                ['representative-both
                 (proposition/conjunction
                  (function/app 'source 'representative)
                  (finite-set/target-equality
                   'B (function/app 'mapping 'representative) 'head))]]
               (let [representative-member
                     (function/app
                      (function/const* 'proposition/left [])
                      (function/app 'source 'representative)
                      (finite-set/target-equality
                       'B (function/app 'mapping 'representative) 'head)
                      'representative-both)
                     representative-image
                     (function/app
                      (function/const* 'proposition/right [])
                      (function/app 'source 'representative)
                      (finite-set/target-equality
                       'B (function/app 'mapping 'representative) 'head)
                      'representative-both)
                     remainder
                     (function/lam
                      [['candidate 'A]]
                      (proposition/conjunction
                       (function/app 'source 'candidate)
                       (proposition/negation
                        (finite-set/equality
                         'A 'candidate 'representative))))
                     remainder-injection
                     (function/lam
                      [['left 'A :implicit]
                       ['left-both (function/app remainder 'left)]
                       ['right 'A :implicit]
                       ['right-both (function/app remainder 'right)]
                       ['same-image
                        (finite-set/target-equality
                         'B (function/app 'mapping 'left)
                         (function/app 'mapping 'right))]]
                      (function/app
                       'injection 'left
                       (function/app
                        (function/const* 'proposition/left [])
                        (function/app 'source 'left)
                        (proposition/negation
                         (finite-set/equality 'A 'left 'representative))
                        'left-both)
                       'right
                       (function/app
                        (function/const* 'proposition/left [])
                        (function/app 'source 'right)
                        (proposition/negation
                         (finite-set/equality 'A 'right 'representative))
                        'right-both)
                       'same-image))
                     remainder-cover
                     (function/lam
                      [['value 'A]
                       ['remainder-both (function/app remainder 'value)]]
                      (let [source-member
                            (function/app
                             (function/const* 'proposition/left [])
                             (function/app 'source 'value)
                             (proposition/negation
                              (finite-set/equality
                               'A 'value 'representative))
                             'remainder-both)
                            not-representative
                            (function/app
                             (function/const* 'proposition/right [])
                             (function/app 'source 'value)
                             (proposition/negation
                              (finite-set/equality
                               'A 'value 'representative))
                             'remainder-both)
                            at-head
                            (finite-set/target-equality
                             'B (function/app 'mapping 'value) 'head)
                            in-tail
                            (finite-set/target-membership
                             'B 'tail (function/app 'mapping 'value))]
                        (function/app
                         (function/const* 'proposition/use-disjunction [])
                         at-head in-tail in-tail
                         (function/app 'source-image-cover
                                       'value source-member)
                         (function/lam
                          [['value-image at-head]]
                          (let [same-image
                                (function/app
                                 (function/const* 'equality/transitive
                                                  [target-data-level])
                                 'B (function/app 'mapping 'value) 'head
                                 (function/app 'mapping 'representative)
                                 'value-image
                                 (function/app
                                  (function/const* 'equality/symmetric
                                                   [target-data-level])
                                  'B
                                  (function/app 'mapping 'representative)
                                  'head representative-image))
                                same-value
                                (function/app
                                 'injection 'value source-member
                                 'representative representative-member
                                 same-image)]
                            (function/app
                             (function/const* 'proposition/explode [])
                             in-tail
                             (function/app not-representative same-value))))
                         (function/lam [['tail-member in-tail]]
                                       'tail-member))))
                     remainder-finite
                     (function/app 'induction-hypothesis
                                   remainder remainder-injection
                                   remainder-cover)
                     inserted
                     (finite-set/insert 'A 'representative remainder)
                     inserted-finite
                     (function/app
                      (function/const* 'set/finite-insert-preserved [U])
                      'A 'representative remainder remainder-finite)
                     inclusion
                     (function/lam
                      [['value 'A]
                       ['source-member (function/app 'source 'value)]]
                      (let [same
                            (finite-set/equality
                             'A 'value 'representative)
                            remainder-member (function/app remainder 'value)]
                        (function/app
                         (function/const* 'logic/classical-cases [])
                         same (function/app inserted 'value)
                         (function/lam
                          [['same-value same]]
                          (function/app
                           (function/const* 'proposition/left-disjunct [])
                           same remainder-member 'same-value))
                         (function/lam
                          [['not-same (proposition/negation same)]]
                          (function/app
                           (function/const* 'proposition/right-disjunct [])
                           same remainder-member
                           (function/app
                            (function/const* 'proposition/conjoin [])
                            (function/app 'source 'value)
                            (proposition/negation same)
                            'source-member 'not-same))))))]
                 (function/app
                  (function/const* 'set/finite-subset-preserved [U])
                  'A 'source inserted inclusion inserted-finite)))))
            (function/lam
             [['no-witness (proposition/negation witness-exists)]]
             (let [tail-cover
                   (function/lam
                    [['value 'A]
                     ['source-member (function/app 'source 'value)]]
                    (let [at-head
                          (finite-set/target-equality
                           'B (function/app 'mapping 'value) 'head)
                          in-tail
                          (finite-set/target-membership
                           'B 'tail (function/app 'mapping 'value))]
                      (function/app
                       (function/const* 'proposition/use-disjunction [])
                       at-head in-tail in-tail
                       (function/app 'source-image-cover
                                     'value 'source-member)
                       (function/lam
                        [['value-image at-head]]
                        (function/app
                         (function/const* 'proposition/explode [])
                         in-tail
                         (function/app
                          'no-witness
                          (function/app
                           (function/const* 'proposition/witness [data-level])
                           'A witness-predicate 'value
                           (function/app
                            (function/const* 'proposition/conjoin [])
                            (function/app 'source 'value) at-head
                            'source-member 'value-image)))))
                       (function/lam [['tail-member in-tail]]
                                     'tail-member))))]
               (function/app 'induction-hypothesis
                             'source 'injection tail-cover))))))]
    {:name 'list/finite-of-injective-enumerated-images
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['enumeration list-b] ['source set-a]
       ['injection (finite-set/injective-on 'A 'B 'mapping 'source)]
       ['source-image-cover
        (image-cover 'A 'enumeration 'mapping 'source)]]
      (finite-set/finite 'A 'source))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)] ['enumeration list-b]]
      (function/app
       (function/const* 'data/List.rec [target-data-level [:zero]])
       'B motive nil-case cons-case 'enumeration))}))

(def finite-of-injection-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        list-b (finite-set/target-list-of 'B)
        target-cover
        (function/lam
         [['enumeration list-b]]
         (finite-set/target-cover 'B 'target 'enumeration))
        result (finite-set/finite 'A 'source)]
    {:name 'set/finite-of-injection-maps-to
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['maps (finite-set/maps-to
               'A 'B 'mapping 'source 'target) :explicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['target-finite (finite-set/target-finite 'B 'target) :explicit]]
      result)
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['maps (finite-set/maps-to
               'A 'B 'mapping 'source 'target) :explicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['target-finite (finite-set/target-finite 'B 'target) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [target-data-level])
       list-b target-cover result 'target-finite
       (function/lam
        [['enumeration list-b]
         ['cover-evidence
          (finite-set/target-cover 'B 'target 'enumeration)]]
        (function/app
         (function/const* 'list/finite-of-injective-enumerated-images
                          [U V])
         'A 'B 'mapping 'enumeration 'source 'injection
         (function/lam
          [['value 'A] ['member (function/app 'source 'value)]]
          (function/app 'cover-evidence
                        (function/app 'mapping 'value)
                        (function/app 'maps 'value 'member)))))))}))

(def finite-of-finite-image-spec
  (let [set-a (finite-set/set-of 'A)
        mapped (finite-set/image 'A 'B 'mapping 'source)
        maps
        (function/lam
         [['value 'A :implicit]
          ['member (function/app 'source 'value) :explicit]]
         (function/app
          (function/const* 'proposition/witness [data-level])
          'A
          (function/lam
           [['input 'A]]
           (proposition/conjunction
            (function/app 'source 'input)
            (finite-set/target-equality
             'B (function/app 'mapping 'input)
             (function/app 'mapping 'value))))
          'value
          (function/app
           (function/const* 'proposition/conjoin [])
           (function/app 'source 'value)
           (finite-set/target-equality
            'B (function/app 'mapping 'value)
            (function/app 'mapping 'value))
           'member
           (function/app
            (function/const* 'equality/reflexive [target-data-level])
            'B (function/app 'mapping 'value)))))]
    {:name 'set/finite-of-finite-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['image-finite (finite-set/target-finite 'B mapped) :explicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (finite-set/finite 'A 'source))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['image-finite (finite-set/target-finite 'B mapped) :explicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (function/app
       (function/const* 'set/finite-of-injection-maps-to [U V])
       'A 'B 'mapping 'source mapped maps 'injection 'image-finite))}))

(def finite-image-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        mapped (finite-set/image 'A 'B 'mapping 'source)
        image-finite (finite-set/target-finite 'B mapped)
        source-finite (finite-set/finite 'A 'source)]
    {:name 'set/finite-image-equivalence
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (proposition/equivalence image-finite source-finite))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       image-finite source-finite
       (function/lam
        [['image-finite-evidence image-finite]]
        (function/app
         (function/const* 'set/finite-of-finite-image [U V])
         'A 'B 'source 'mapping 'image-finite-evidence 'injection))
       (function/lam
        [['source-finite-evidence source-finite]]
        (function/app
         (function/const* 'set/finite-image-preserved [U V])
         'A 'B 'source 'mapping 'source-finite-evidence))))}))

(def infinite-image-spec
  (let [set-a (finite-set/set-of 'A)
        mapped (finite-set/image 'A 'B 'mapping 'source)]
    {:name 'set/infinite-image-preserved
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]]
      (finite-set/target-infinite 'B mapped))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['image-finite (finite-set/target-finite 'B mapped)]]
      (function/app
       'source-infinite
       (function/app
        (function/const* 'set/finite-of-finite-image [U V])
        'A 'B 'source 'mapping 'image-finite 'injection)))}))

(def infinite-image-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        mapped (finite-set/image 'A 'B 'mapping 'source)
        image-infinite (finite-set/target-infinite 'B mapped)
        source-infinite (finite-set/infinite 'A 'source)]
    {:name 'set/infinite-image-equivalence
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (proposition/equivalence image-infinite source-infinite))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       image-infinite source-infinite
       (function/lam
        [['image-infinite-evidence image-infinite]]
        (function/app
         (function/const* 'set/infinite-of-image [U V])
         'A 'B 'mapping 'source 'image-infinite-evidence))
       (function/lam
        [['source-infinite-evidence source-infinite]]
        (function/app
         (function/const* 'set/infinite-image-preserved [U V])
         'A 'B 'source 'mapping 'injection
         'source-infinite-evidence))))}))

(def infinite-of-injection-maps-to-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)]
    {:name 'set/infinite-of-injection-maps-to
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['maps (finite-set/maps-to
               'A 'B 'mapping 'source 'target) :explicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]]
      (finite-set/target-infinite 'B 'target))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping 'source) :explicit]
       ['maps (finite-set/maps-to
               'A 'B 'mapping 'source 'target) :explicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['target-finite (finite-set/target-finite 'B 'target)]]
      (function/app
       'source-infinite
       (function/app
        (function/const* 'set/finite-of-injection-maps-to [U V])
        'A 'B 'mapping 'source 'target
        'maps 'injection 'target-finite)))}))

(def not-injective-on-infinite-finite-image-spec
  (let [set-a (finite-set/set-of 'A)
        mapped (finite-set/image 'A 'B 'mapping 'source)
        injection (finite-set/injective-on 'A 'B 'mapping 'source)]
    {:name 'set/not-injective-on-infinite-finite-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['image-finite (finite-set/target-finite 'B mapped) :explicit]]
      (proposition/negation injection))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['image-finite (finite-set/target-finite 'B mapped) :explicit]
       ['injection injection]]
      (function/app
       'source-infinite
       (function/app
        (function/const* 'set/finite-of-finite-image [U V])
        'A 'B 'source 'mapping 'image-finite 'injection)))}))

(def bijective-finite-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        source-finite (finite-set/finite 'A 'source)
        target-finite (finite-set/target-finite 'B 'target)
        maps (finite-set/maps-to 'A 'B 'mapping 'source 'target)
        injection (finite-set/injective-on 'A 'B 'mapping 'source)
        surjection
        (finite-set/surjective-on 'A 'B 'mapping 'source 'target)
        bijection
        (function/app (function/const* 'set/bijective-on [U V])
                      'A 'B 'mapping 'source 'target)]
    {:name 'set/bijective-finite-equivalence
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['bijection bijection :explicit]]
      (proposition/equivalence source-finite target-finite))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['source set-a :implicit] ['target set-b :implicit]
       ['bijection bijection :explicit]]
      (let [maps-evidence
            (function/app
             (function/const* 'proposition/left [])
             maps (proposition/conjunction injection surjection) 'bijection)
            injective-surjective
            (function/app
             (function/const* 'proposition/right [])
             maps (proposition/conjunction injection surjection) 'bijection)
            injection-evidence
            (function/app
             (function/const* 'proposition/left [])
             injection surjection injective-surjective)
            surjection-evidence
            (function/app
             (function/const* 'proposition/right [])
             injection surjection injective-surjective)]
        (function/app
         (function/const* 'proposition/equivalence-intro [])
         source-finite target-finite
         (function/lam
          [['source-finite-evidence source-finite]]
          (function/app
           (function/const* 'set/finite-of-surjection [U V])
           'A 'B 'source 'target 'mapping
           surjection-evidence 'source-finite-evidence))
         (function/lam
          [['target-finite-evidence target-finite]]
          (function/app
           (function/const* 'set/finite-of-injection-maps-to [U V])
           'A 'B 'mapping 'source 'target
           maps-evidence injection-evidence
           'target-finite-evidence)))))}))

(def infinite-difference-spec
  (let [set-a (finite-set/set-of 'A)
        difference (finite-set/difference 'A 'source 'removed)
        joined (finite-set/union 'A difference 'removed)]
    {:name 'set/infinite-difference-finite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source set-a :implicit] ['removed set-a :implicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['removed-finite (finite-set/finite 'A 'removed) :explicit]]
      (finite-set/infinite 'A difference))
     :value
     (function/lam
      [['A type-u :implicit]
       ['source set-a :implicit] ['removed set-a :implicit]
       ['source-infinite (finite-set/infinite 'A 'source) :explicit]
       ['removed-finite (finite-set/finite 'A 'removed) :explicit]
       ['difference-finite (finite-set/finite 'A difference)]]
      (let [joined-finite
            (function/app
             (function/const* 'set/finite-union-preserved [U])
             'A difference 'removed 'difference-finite 'removed-finite)
            inclusion
            (function/lam
             [['value 'A]
              ['source-member (function/app 'source 'value)]]
             (let [removed-member (function/app 'removed 'value)
                   difference-member
                   (proposition/conjunction
                    (function/app 'source 'value)
                    (proposition/negation removed-member))]
               (function/app
                (function/const* 'logic/classical-cases [])
                removed-member (function/app joined 'value)
                (function/lam
                 [['member removed-member]]
                 (function/app
                  (function/const* 'proposition/right-disjunct [])
                  difference-member removed-member 'member))
                (function/lam
                 [['not-member (proposition/negation removed-member)]]
                 (function/app
                  (function/const* 'proposition/left-disjunct [])
                  difference-member removed-member
                  (function/app
                   (function/const* 'proposition/conjoin [])
                   (function/app 'source 'value)
                   (proposition/negation removed-member)
                   'source-member 'not-member))))))]
        (function/app
         'source-infinite
         (function/app
          (function/const* 'set/finite-subset-preserved [U])
          'A 'source joined inclusion joined-finite))))}))

(def finite-preimage-under-injection-spec
  (let [set-b (finite-set/target-set-of 'B)
        source (finite-set/preimage 'A 'B 'mapping 'target)
        maps
        (function/lam
         [['value 'A :implicit]
          ['member (function/app source 'value) :explicit]]
         'member)]
    {:name 'set/finite-preimage-under-injection
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['target set-b :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping source) :explicit]
       ['target-finite
        (finite-set/target-finite 'B 'target) :explicit]]
      (finite-set/finite 'A source))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['target set-b :implicit]
       ['injection
        (finite-set/injective-on 'A 'B 'mapping source) :explicit]
       ['target-finite
        (finite-set/target-finite 'B 'target) :explicit]]
      (function/app
       (function/const* 'set/finite-of-injection-maps-to [U V])
       'A 'B 'mapping source 'target maps
       'injection 'target-finite))}))

(def theorem-specs
  [finite-injective-enumeration-spec finite-of-injection-spec
   finite-of-finite-image-spec finite-image-equivalence-spec
   infinite-image-spec infinite-image-equivalence-spec
   infinite-of-injection-maps-to-spec
   not-injective-on-infinite-finite-image-spec
   bijective-finite-equivalence-spec infinite-difference-spec
   finite-preimage-under-injection-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Classical finite-set theorem failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-theorem [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native
           :producer :classical-finite-set-transport
           :logical/profile :classical}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Classical finite-set theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (when-not (and (environment/resolve-id checked-environment
                                        'logic/classical-cases)
                 (environment/resolve-id checked-environment
                                        'logic/excluded-middle))
    (throw (ex-info "Classical finite-set transport requires activation"
                    {:error/category :finite-set/classical-profile-required})))
  (reduce add-theorem checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
