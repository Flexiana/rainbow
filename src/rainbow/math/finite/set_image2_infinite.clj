(ns rainbow.math.finite.set-image2-infinite
  "Infinitude transport through binary images and Cartesian products."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U finite-set/U)
(def V finite-set/V)
(def W finite-set/W)
(def data-level finite-set/data-level)
(def target-data-level finite-set/target-data-level)
(def output-data-level finite-set/output-data-level)
(def product-level finite-set/product-level)
(def type-u finite-set/type-u)
(def type-v finite-set/type-v)
(def type-w finite-set/type-w)

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- conjoin [left right left-evidence right-evidence]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-evidence right-evidence))

(defn- left [left right evidence]
  (function/app (function/const* 'proposition/left [])
                left right evidence))

(defn- right [left right evidence]
  (function/app (function/const* 'proposition/right [])
                left right evidence))

(defn- injective-on
  [source-level target-level source-element target-element mapping source]
  (function/app (function/const* 'set/injective-on
                                 [source-level target-level])
                source-element target-element mapping source))

(defn- maps-to
  [source-level target-level source-element target-element mapping source
   target]
  (function/app (function/const* 'set/maps-to [source-level target-level])
                source-element target-element mapping source target))

(defn- infinite-at [level element source]
  (function/app (function/const* 'set/infinite [level]) element source))

(defn- nonempty-at [level element source]
  (function/app (function/const* 'set/nonempty [level]) element source))

(defn- left-section [mapping selected-right]
  (function/lam
   [['left-value 'A]]
   (function/app mapping 'left-value selected-right)))

(defn- right-section [mapping selected-left]
  (function/lam
   [['right-value 'B]]
   (function/app mapping selected-left 'right-value)))

(defn- image2-left-maps [mapping left right selected-right mapped]
  (let [section (left-section mapping selected-right)]
    (function/lam
     [['value 'A :implicit]
      ['left-member (function/app left 'value) :explicit]]
     (witness
      data-level 'A
      (function/lam
       [['left-input 'A]]
       (proposition/conjunction
        (function/app left 'left-input)
        (proposition/existence
         target-data-level 'B
         (function/lam
          [['right-input 'B]]
          (proposition/conjunction
           (function/app right 'right-input)
           (finite-set/output-equality
            'C (function/app mapping 'left-input 'right-input)
            (function/app section 'value)))))))
      'value
      (conjoin
       (function/app left 'value)
       (proposition/existence
        target-data-level 'B
        (function/lam
         [['right-input 'B]]
         (proposition/conjunction
          (function/app right 'right-input)
          (finite-set/output-equality
           'C (function/app mapping 'value 'right-input)
           (function/app section 'value)))))
       'left-member
       (witness
        target-data-level 'B
        (function/lam
         [['right-input 'B]]
         (proposition/conjunction
          (function/app right 'right-input)
          (finite-set/output-equality
           'C (function/app mapping 'value 'right-input)
           (function/app section 'value))))
        selected-right
        (conjoin
         (function/app right selected-right)
         (finite-set/output-equality
          'C (function/app mapping 'value selected-right)
          (function/app section 'value))
         'selected-member
         (function/app
          (function/const* 'equality/reflexive [output-data-level])
          'C (function/app mapping 'value selected-right)))))))))

(defn- image2-right-maps [mapping left right selected-left mapped]
  (let [section (right-section mapping selected-left)]
    (function/lam
     [['value 'B :implicit]
      ['right-member (function/app right 'value) :explicit]]
     (witness
      data-level 'A
      (function/lam
       [['left-input 'A]]
       (proposition/conjunction
        (function/app left 'left-input)
        (proposition/existence
         target-data-level 'B
         (function/lam
          [['right-input 'B]]
          (proposition/conjunction
           (function/app right 'right-input)
           (finite-set/output-equality
            'C (function/app mapping 'left-input 'right-input)
            (function/app section 'value)))))))
      selected-left
      (conjoin
       (function/app left selected-left)
       (proposition/existence
        target-data-level 'B
        (function/lam
         [['right-input 'B]]
         (proposition/conjunction
          (function/app right 'right-input)
          (finite-set/output-equality
           'C (function/app mapping selected-left 'right-input)
           (function/app section 'value)))))
       'selected-member
       (witness
        target-data-level 'B
        (function/lam
         [['right-input 'B]]
         (proposition/conjunction
          (function/app right 'right-input)
          (finite-set/output-equality
           'C (function/app mapping selected-left 'right-input)
           (function/app section 'value))))
        'value
        (conjoin
         (function/app right 'value)
         (finite-set/output-equality
          'C (function/app mapping selected-left 'value)
          (function/app section 'value))
         'right-member
         (function/app
          (function/const* 'equality/reflexive [output-data-level])
          'C (function/app mapping selected-left 'value)))))))))

(def infinite-image2-left-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        mapped (finite-set/image2 'A 'B 'C 'mapping 'left 'right)
        section (left-section 'mapping 'selected-right)
        injection (injective-on U W 'A 'C section 'left)]
    {:name 'set/infinite-image2-left
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['selected-right 'B :implicit]
       ['left-infinite (finite-set/infinite 'A 'left) :explicit]
       ['selected-member (function/app 'right 'selected-right) :explicit]
       ['injection injection :explicit]]
      (infinite-at W 'C mapped))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['selected-right 'B :implicit]
       ['left-infinite (finite-set/infinite 'A 'left) :explicit]
       ['selected-member (function/app 'right 'selected-right) :explicit]
       ['injection injection :explicit]]
      (function/app
       (function/const* 'set/infinite-of-injection-maps-to [U W])
       'A 'C 'left mapped section 'injection
       (image2-left-maps 'mapping 'left 'right 'selected-right mapped)
       'left-infinite))}))

(def infinite-image2-right-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        mapped (finite-set/image2 'A 'B 'C 'mapping 'left 'right)
        section (right-section 'mapping 'selected-left)
        injection (injective-on V W 'B 'C section 'right)]
    {:name 'set/infinite-image2-right
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['selected-left 'A :implicit]
       ['right-infinite (finite-set/target-infinite 'B 'right) :explicit]
       ['selected-member (function/app 'left 'selected-left) :explicit]
       ['injection injection :explicit]]
      (infinite-at W 'C mapped))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['selected-left 'A :implicit]
       ['right-infinite (finite-set/target-infinite 'B 'right) :explicit]
       ['selected-member (function/app 'left 'selected-left) :explicit]
       ['injection injection :explicit]]
      (function/app
       (function/const* 'set/infinite-of-injection-maps-to [V W])
       'B 'C 'right mapped section 'injection
       (image2-right-maps 'mapping 'left 'right 'selected-left mapped)
       'right-infinite))}))

(defn- mapped-nonempty-components
  [mapped mapping left-set right-set target continuation]
  (function/app
   (function/const* 'proposition/use-witness [output-data-level])
   'C mapped target
   (function/app
    (function/const* 'set/infinite-nonempty [W])
    'C mapped 'mapped-infinite)
   (function/lam
    [['output 'C] ['mapped-member (function/app mapped 'output)]]
    (let [left-predicate
          (function/lam
           [['left-value 'A]]
           (proposition/conjunction
            (function/app left-set 'left-value)
            (proposition/existence
             target-data-level 'B
             (function/lam
              [['right-value 'B]]
              (proposition/conjunction
               (function/app right-set 'right-value)
               (finite-set/output-equality
                'C (function/app mapping 'left-value 'right-value)
                'output))))))]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A left-predicate target 'mapped-member
       (function/lam
        [['left-value 'A]
         ['left-both (function/app left-predicate 'left-value)]]
        (let [left-member
              (left (function/app left-set 'left-value)
                    (proposition/existence
                     target-data-level 'B
                     (function/lam
                      [['right-value 'B]]
                      (proposition/conjunction
                       (function/app right-set 'right-value)
                       (finite-set/output-equality
                        'C
                        (function/app mapping 'left-value 'right-value)
                        'output))))
                    'left-both)
              right-exists
              (right (function/app left-set 'left-value)
                     (proposition/existence
                      target-data-level 'B
                      (function/lam
                       [['right-value 'B]]
                       (proposition/conjunction
                        (function/app right-set 'right-value)
                        (finite-set/output-equality
                         'C
                         (function/app mapping 'left-value 'right-value)
                         'output))))
                     'left-both)]
          (function/app
           (function/const* 'proposition/use-witness [target-data-level])
           'B
           (function/lam
            [['right-value 'B]]
            (proposition/conjunction
             (function/app right-set 'right-value)
             (finite-set/output-equality
              'C (function/app mapping 'left-value 'right-value) 'output)))
           target right-exists
           (function/lam
            [['right-value 'B]
             ['right-both
              (proposition/conjunction
               (function/app right-set 'right-value)
               (finite-set/output-equality
                'C (function/app mapping 'left-value 'right-value)
                'output))]]
            (function/app
             continuation 'left-value left-member 'right-value
             (left
              (function/app right-set 'right-value)
              (finite-set/output-equality
               'C (function/app mapping 'left-value 'right-value) 'output)
              'right-both)))))))))))

(def infinite-image2-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        mapped (finite-set/image2 'A 'B 'C 'mapping 'left 'right)
        mapped-infinite (infinite-at W 'C mapped)
        left-infinite (finite-set/infinite 'A 'left)
        right-infinite (finite-set/target-infinite 'B 'right)
        left-nonempty (finite-set/nonempty 'A 'left)
        right-nonempty (finite-set/target-nonempty 'B 'right)
        left-case (proposition/conjunction left-infinite right-nonempty)
        right-case (proposition/conjunction right-infinite left-nonempty)
        either (proposition/disjunction left-case right-case)
        left-injections
        (function/forall
         [['selected-right 'B]
          ['selected-member (function/app 'right 'selected-right)]]
         (injective-on U W 'A 'C
                       (left-section 'mapping 'selected-right) 'left))
        right-injections
        (function/forall
         [['selected-left 'A]
          ['selected-member (function/app 'left 'selected-left)]]
         (injective-on V W 'B 'C
                       (right-section 'mapping 'selected-left) 'right))]
    {:name 'set/infinite-image2-equivalence
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['left-injections left-injections :explicit]
       ['right-injections right-injections :explicit]]
      (proposition/equivalence mapped-infinite either))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit] ['C type-w :implicit]
       ['mapping (function/arrow 'A 'B 'C) :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['left-injections left-injections :explicit]
       ['right-injections right-injections :explicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       mapped-infinite either
       (function/lam
        [['mapped-infinite mapped-infinite]]
        (mapped-nonempty-components
         mapped 'mapping 'left 'right either
         (function/lam
          [['left-value 'A]
           ['left-member (function/app 'left 'left-value)]
           ['right-value 'B]
           ['right-member (function/app 'right 'right-value)]]
          (let [left-nonempty-evidence
                (witness data-level 'A 'left 'left-value 'left-member)
                right-nonempty-evidence
                (witness target-data-level 'B 'right
                         'right-value 'right-member)]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             left-infinite (finite-set/finite 'A 'left) either
             (function/app
              (function/const* 'set/infinite-or-finite [U])
              'A 'left)
             (function/lam
              [['left-infinite-evidence left-infinite]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               left-case right-case
               (conjoin left-infinite right-nonempty
                        'left-infinite-evidence
                        right-nonempty-evidence)))
             (function/lam
              [['left-finite (finite-set/finite 'A 'left)]]
              (function/app
               (function/const* 'proposition/use-disjunction [])
               right-infinite (finite-set/target-finite 'B 'right) either
               (function/app
                (function/const* 'set/infinite-or-finite [V])
                'B 'right)
               (function/lam
                [['right-infinite-evidence right-infinite]]
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 left-case right-case
                 (conjoin right-infinite left-nonempty
                          'right-infinite-evidence
                          left-nonempty-evidence)))
               (function/lam
                [['right-finite (finite-set/target-finite 'B 'right)]]
                (function/app
                 (function/const* 'proposition/explode [])
                 either
                 (function/app
                  'mapped-infinite
                  (function/app
                   (function/const* 'set/finite-image2-preserved [U V W])
                   'A 'B 'C 'left 'right 'mapping
                   'left-finite 'right-finite)))))))))))
       (function/lam
        [['either-evidence either]]
        (function/app
         (function/const* 'proposition/use-disjunction [])
         left-case right-case mapped-infinite 'either-evidence
         (function/lam
          [['left-both left-case]]
          (function/app
           (function/const* 'proposition/use-witness [target-data-level])
           'B 'right mapped-infinite
           (right left-infinite right-nonempty 'left-both)
           (function/lam
            [['selected-right 'B]
             ['selected-member (function/app 'right 'selected-right)]]
            (function/app
             (function/const* 'set/infinite-image2-left [U V W])
             'A 'B 'C 'mapping 'left 'right 'selected-right
             (left left-infinite right-nonempty 'left-both)
             'selected-member
             (function/app 'left-injections
                           'selected-right 'selected-member)))))
         (function/lam
          [['right-both right-case]]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A 'left mapped-infinite
           (right right-infinite left-nonempty 'right-both)
           (function/lam
            [['selected-left 'A]
             ['selected-member (function/app 'left 'selected-left)]]
            (function/app
             (function/const* 'set/infinite-image2-right [U V W])
             'A 'B 'C 'mapping 'left 'right 'selected-left
             (left right-infinite left-nonempty 'right-both)
             'selected-member
             (function/app 'right-injections
                           'selected-left 'selected-member)))))))))}))

(def infinite-product-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        set-b (finite-set/target-set-of 'B)
        product (finite-set/product-type 'A 'B)
        product-set (finite-set/product-set 'A 'B 'left 'right)
        product-infinite (infinite-at product-level product product-set)
        left-infinite (finite-set/infinite 'A 'left)
        right-infinite (finite-set/target-infinite 'B 'right)
        left-nonempty (finite-set/nonempty 'A 'left)
        right-nonempty (finite-set/target-nonempty 'B 'right)
        left-case (proposition/conjunction left-infinite right-nonempty)
        right-case (proposition/conjunction right-infinite left-nonempty)
        either (proposition/disjunction left-case right-case)]
    {:name 'set/infinite-product-equivalence
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]]
      (proposition/equivalence product-infinite either))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       product-infinite either
       (function/lam
        [['product-infinite product-infinite]]
        (function/app
         (function/const* 'proposition/use-witness
                          [[:succ product-level]])
         product product-set either
         (function/app
          (function/const* 'set/infinite-nonempty [product-level])
          product product-set 'product-infinite)
         (function/lam
          [['pair product] ['pair-member (function/app product-set 'pair)]]
          (let [left-value (finite-set/first-value 'A 'B 'pair)
                right-value (finite-set/second-value 'A 'B 'pair)
                left-member
                (left (function/app 'left left-value)
                      (function/app 'right right-value) 'pair-member)
                right-member
                (right (function/app 'left left-value)
                       (function/app 'right right-value) 'pair-member)
                left-nonempty-evidence
                (witness data-level 'A 'left left-value left-member)
                right-nonempty-evidence
                (witness target-data-level 'B 'right
                         right-value right-member)]
            (function/app
             (function/const* 'proposition/use-disjunction [])
             left-infinite (finite-set/finite 'A 'left) either
             (function/app
              (function/const* 'set/infinite-or-finite [U]) 'A 'left)
             (function/lam
              [['left-infinite-evidence left-infinite]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               left-case right-case
               (conjoin left-infinite right-nonempty
                        'left-infinite-evidence right-nonempty-evidence)))
             (function/lam
              [['left-finite (finite-set/finite 'A 'left)]]
              (function/app
               (function/const* 'proposition/use-disjunction [])
               right-infinite (finite-set/target-finite 'B 'right) either
               (function/app
                (function/const* 'set/infinite-or-finite [V]) 'B 'right)
               (function/lam
                [['right-infinite-evidence right-infinite]]
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 left-case right-case
                 (conjoin right-infinite left-nonempty
                          'right-infinite-evidence left-nonempty-evidence)))
               (function/lam
                [['right-finite (finite-set/target-finite 'B 'right)]]
                (function/app
                 (function/const* 'proposition/explode [])
                 either
                 (function/app
                  'product-infinite
                  (function/app
                   (function/const* 'set/finite-product-preserved [U V])
                   'A 'B 'left 'right
                   'left-finite 'right-finite)))))))))))
       (function/lam
        [['either-evidence either]]
        (function/app
         (function/const* 'proposition/use-disjunction [])
         left-case right-case product-infinite 'either-evidence
         (function/lam
          [['left-both left-case]]
          (function/app
           (function/const* 'set/infinite-product-left [U V])
           'A 'B 'left 'right
           (left left-infinite right-nonempty 'left-both)
           (right left-infinite right-nonempty 'left-both)))
         (function/lam
          [['right-both right-case]]
          (function/app
           (function/const* 'set/infinite-product-right [U V])
           'A 'B 'left 'right
           (left right-infinite left-nonempty 'right-both)
           (right right-infinite left-nonempty 'right-both)))))))}))

(def theorem-specs
  [infinite-image2-left-spec infinite-image2-right-spec
   infinite-image2-equivalence-spec infinite-product-equivalence-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Infinite image/product theorem failed elaboration"
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
          {:origin :native :producer :finite-set-image2-infinite-algebra}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Infinite image/product theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (doseq [required ['set/infinite-of-injection-maps-to
                    'set/infinite-or-finite 'set/infinite-nonempty
                    'set/finite-image2-preserved
                    'set/finite-product-preserved
                    'set/infinite-product-left 'set/infinite-product-right]]
    (when-not (environment/resolve-id checked-environment required)
      (throw (ex-info "Infinite image/product dependency is unavailable"
                      {:error/category
                       :finite-set/image2-infinite-dependency-missing
                       :required required}))))
  (reduce add-theorem checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
