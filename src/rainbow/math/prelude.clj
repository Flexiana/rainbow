(ns rainbow.math.prelude
  "Native, data-oriented concepts selected from corpus nativeization failures."
  (:require [rainbow.module :as module]
            [rainbow.data.inductive :as inductive]
            [rainbow.data.list :as list-data]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def X [:param 'x])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])
(def type-u [:sort [:succ U]])
(def type-v [:sort [:succ V]])
(def type-w [:sort [:succ W]])
(def type-x [:sort [:succ X]])

(defn- eq [level carrier left right]
  (function/equality level carrier left right))

(def concept-specs
  [{:name 'function/identity
    :universes ['u]
    :type (function/forall [['A sort-u]] (function/arrow 'A 'A))
    :value (function/lam [['A sort-u] ['value 'A]] 'value)}

   {:name 'function/compose
    :universes ['u 'v 'w]
    :type
    (function/forall
     [['A sort-u] ['B sort-v] ['C sort-w]]
     (function/arrow (function/arrow 'B 'C)
                     (function/arrow 'A 'B)
                     (function/arrow 'A 'C)))
    :value
    (function/lam
     [['A sort-u] ['B sort-v] ['C sort-w]
      ['outer (function/arrow 'B 'C)] ['inner (function/arrow 'A 'B)]
      ['value 'A]]
     (function/app 'outer (function/app 'inner 'value)))}

   {:name 'function/left-inverse
    :universes ['u 'v]
    :type
    (function/forall
     [['A sort-u] ['B sort-v]
      ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]]
     'Prop)
    :value
    (function/lam
     [['A sort-u] ['B sort-v]
      ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]]
     (function/forall
      [['value 'A]]
      (eq U 'A (function/app 'backward (function/app 'forward 'value))
          'value)))}

   {:name 'function/right-inverse
    :universes ['u 'v]
    :type
    (function/forall
     [['A sort-u] ['B sort-v]
      ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]]
     'Prop)
    :value
    (function/lam
     [['A sort-u] ['B sort-v]
      ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]]
     (function/forall
      [['value 'B]]
      (eq V 'B (function/app 'forward (function/app 'backward 'value))
          'value)))}

   {:name 'proposition/nonempty
    :universes ['u]
    :type (function/forall [['A sort-u]] 'Prop)
    :value
    (function/lam
     [['A sort-u]]
     (function/forall
      [['P 'Prop] ['consume (function/arrow 'A 'P)]] 'P))}

   {:name 'proposition/is-empty
    :universes ['u]
    :type (function/forall [['A sort-u]] 'Prop)
    :value
    (function/lam [['A sort-u]]
                  (function/arrow 'A
                                  (function/const* 'proposition/falsity [])))}])

(def combinator-specs
  [{:name 'proposition/xor
    :universes []
    :type (function/arrow 'Prop 'Prop 'Prop)
   :value
    (function/lam
     [['left 'Prop] ['right 'Prop]]
     (proposition/disjunction
      (proposition/conjunction 'left (proposition/negation 'right))
      (proposition/conjunction (proposition/negation 'left) 'right)))}

   {:name 'relation/symmetric
    :universes ['u]
    :type
    (function/forall
     [['A sort-u] ['relation (function/arrow 'A 'A 'Prop)]] 'Prop)
    :value
    (function/lam
     [['A sort-u] ['relation (function/arrow 'A 'A 'Prop)]]
     (function/forall
      [['left 'A] ['right 'A]
       ['evidence (function/app 'relation 'left 'right)]]
      (function/app 'relation 'right 'left)))}

   {:name 'function/commute
    :universes ['u]
    :type
    (function/forall
     [['A type-u] ['left (function/arrow 'A 'A)]
      ['right (function/arrow 'A 'A)]] 'Prop)
    :value
    (function/lam
     [['A type-u] ['left (function/arrow 'A 'A)]
      ['right (function/arrow 'A 'A)]]
     (function/forall
      [['value 'A]]
      (eq [:succ U] 'A
          (function/app 'left (function/app 'right 'value))
          (function/app 'right (function/app 'left 'value)))))}

   {:name 'function/semiconjugate
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v]
      ['map (function/arrow 'A 'B)]
      ['source (function/arrow 'A 'A)]
      ['target (function/arrow 'B 'B)]] 'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v]
      ['map (function/arrow 'A 'B)]
      ['source (function/arrow 'A 'A)]
      ['target (function/arrow 'B 'B)]]
     (function/forall
      [['value 'A]]
      (eq [:succ V] 'B
          (function/app 'map (function/app 'source 'value))
          (function/app 'target (function/app 'map 'value)))))}

   {:name 'function/fixed-point
    :universes ['u]
    :type
    (function/forall
     [['A type-u] ['callable (function/arrow 'A 'A)] ['value 'A]] 'Prop)
    :value
    (function/lam
     [['A type-u] ['callable (function/arrow 'A 'A)] ['value 'A]]
     (eq [:succ U] 'A (function/app 'callable 'value) 'value))}

   {:name 'function/on-results
    :universes ['u 'v 'w]
    :type
    (function/forall
     [['A sort-u] ['B sort-v] ['C sort-w]
      ['combine (function/arrow 'B 'B 'C)]
      ['map (function/arrow 'A 'B)]]
     (function/arrow 'A 'A 'C))
    :value
    (function/lam
     [['A sort-u] ['B sort-v] ['C sort-w]
      ['combine (function/arrow 'B 'B 'C)]
      ['map (function/arrow 'A 'B)] ['left 'A] ['right 'A]]
     (function/app 'combine (function/app 'map 'left)
                   (function/app 'map 'right)))}

   {:name 'proposition/nonempty-intro
    :universes ['u]
    :type
    (function/forall
     [['A sort-u] ['value 'A]]
     (function/app (function/const* 'proposition/nonempty [U]) 'A))
    :value
    (function/lam
     [['A sort-u] ['value 'A] ['P 'Prop]
      ['consume (function/arrow 'A 'P)]]
     (function/app 'consume 'value))}])

(def option-spec
  {:block/schema-version 1
   :block/alias 'data/Option
   :block/universes ['u]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}]
   :block/sort-level U
   :block/constructors
   [{:constructor/alias 'data/none :constructor/fields []}
    {:constructor/alias 'data/some
     :constructor/fields [{:field/name 'value :field/type [:var 'A]}]}]})

(def subtype-spec
  {:block/schema-version 1
   :block/alias 'data/Subtype
   :block/universes ['u]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}
    {:parameter/name 'predicate
     :parameter/type [:pi [['value [:var 'A]]] [:sort [:zero]]]}]
   :block/sort-level [:max [:succ [:zero]] U]
   :block/constructors
   [{:constructor/alias 'data/subtype
     :constructor/fields
     [{:field/name 'value :field/type [:var 'A]}
      {:field/name 'property
       :field/type [:app [:var 'predicate] [:var 'value]]}]}]})

(def sigma-spec
  {:block/schema-version 1
   :block/alias 'data/Sigma
   :block/universes ['u 'v]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort [:succ U]]}
    {:parameter/name 'B
     :parameter/type [:pi [['value [:var 'A]]] [:sort [:succ V]]]}]
   :block/sort-level [:succ [:max U V]]
   :block/constructors
   [{:constructor/alias 'data/sigma
     :constructor/fields
     [{:field/name 'first :field/type [:var 'A]}
      {:field/name 'second :field/type [:app [:var 'B] [:var 'first]]}]}]})

(def psigma-spec
  {:block/schema-version 1
   :block/alias 'data/PSigma
   :block/universes ['u 'v]
   :block/parameters
   [{:parameter/name 'A :parameter/type [:sort U]}
    {:parameter/name 'B
     :parameter/type [:pi [['value [:var 'A]]] [:sort V]]}]
   :block/sort-level [:max [:max [:succ [:zero]] U] V]
   :block/constructors
   [{:constructor/alias 'data/psigma
     :constructor/fields
     [{:field/name 'first :field/type [:var 'A]}
      {:field/name 'second :field/type [:app [:var 'B] [:var 'first]]}]}]})

(def subtype-definition-specs
  [{:name 'subtype/value
    :universes ['u]
    :type
    (function/forall
     [['A sort-u] ['predicate (function/arrow 'A 'Prop)]
      ['source
       (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
     'A)
    :value
    (function/lam
     [['A sort-u] ['predicate (function/arrow 'A 'Prop)]
      ['source
       (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
     (function/app
      (function/const* 'data/Subtype.rec [U U])
      'A 'predicate
      (function/lam
       [['ignored
         (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
       'A)
      (function/lam
       [['value 'A] ['property (function/app 'predicate 'value)]] 'value)
      'source))}

   {:name 'subtype/property
    :universes ['u]
    :type
    (function/forall
     [['A sort-u] ['predicate (function/arrow 'A 'Prop)]
      ['source
       (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
     (function/app
      'predicate
      (function/app (function/const* 'subtype/value [U])
                    'A 'predicate 'source)))
    :value
    (function/lam
     [['A sort-u] ['predicate (function/arrow 'A 'Prop)]
      ['source
       (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
     (function/app
      (function/const* 'data/Subtype.rec [U [:zero]])
      'A 'predicate
      (function/lam
       [['candidate
         (function/app (function/const* 'data/Subtype [U]) 'A 'predicate)]]
       (function/app
        'predicate
        (function/app (function/const* 'subtype/value [U])
                      'A 'predicate 'candidate)))
      (function/lam
       [['value 'A] ['property (function/app 'predicate 'value)]] 'property)
      'source))}

   {:name 'set/element-type
    :universes ['u]
    :type
    (function/forall
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     [:sort [:succ U]])
    :value
    (function/lam
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/app (function/const* 'data/Subtype [[:succ U]])
                   'A 'source))}])

(def dependent-sum-definition-specs
  (let [sigma-type
        (fn [a b] (function/app (function/const* 'data/Sigma [U V]) a b))
        psigma-type
        (fn [a b] (function/app (function/const* 'data/PSigma [U V]) a b))]
    [{:name 'sigma/first
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (sigma-type 'A 'B)]] 'A)
      :value
      (function/lam
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (sigma-type 'A 'B)]]
       (function/app
        (function/const* 'data/Sigma.rec [U V [:succ U]])
        'A 'B (function/lam [['ignored (sigma-type 'A 'B)]] 'A)
        (function/lam
         [['first 'A] ['second (function/app 'B 'first)]] 'first)
        'source))}

     {:name 'sigma/second
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (sigma-type 'A 'B)]]
       (function/app
        'B (function/app (function/const* 'sigma/first [U V])
                         'A 'B 'source)))
      :value
      (function/lam
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (sigma-type 'A 'B)]]
       (function/app
        (function/const* 'data/Sigma.rec [U V [:succ V]])
        'A 'B
        (function/lam
         [['candidate (sigma-type 'A 'B)]]
         (function/app
          'B (function/app (function/const* 'sigma/first [U V])
                           'A 'B 'candidate)))
        (function/lam
         [['first 'A] ['second (function/app 'B 'first)]] 'second)
        'source))}

     {:name 'psigma/first
      :universes ['u 'v]
      :type
      (function/forall
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['source (psigma-type 'A 'B)]] 'A)
      :value
      (function/lam
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['source (psigma-type 'A 'B)]]
       (function/app
        (function/const* 'data/PSigma.rec [U V U])
        'A 'B (function/lam [['ignored (psigma-type 'A 'B)]] 'A)
        (function/lam
         [['first 'A] ['second (function/app 'B 'first)]] 'first)
        'source))}

     {:name 'psigma/second
      :universes ['u 'v]
      :type
      (function/forall
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['source (psigma-type 'A 'B)]]
       (function/app
        'B (function/app (function/const* 'psigma/first [U V])
                         'A 'B 'source)))
      :value
      (function/lam
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['source (psigma-type 'A 'B)]]
       (function/app
        (function/const* 'data/PSigma.rec [U V V])
        'A 'B
        (function/lam
         [['candidate (psigma-type 'A 'B)]]
         (function/app
          'B (function/app (function/const* 'psigma/first [U V])
                           'A 'B 'candidate)))
        (function/lam
         [['first 'A] ['second (function/app 'B 'first)]] 'second)
        'source))}]))

(def collection-specs
  [{:name 'set/Set
   :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     [:sort [:max [:succ [:zero]] [:succ U]]])
    :value (function/lam [['A type-u]] (function/arrow 'A 'Prop))}

   {:name 'membership/member
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u]
      ['Container [:sort [:max [:succ [:zero]] [:succ V]]]]
      ['dictionary (function/arrow 'Container 'A 'Prop)]
      ['container 'Container] ['value 'A]]
     'Prop)
    :value
    (function/lam
     [['A type-u]
      ['Container [:sort [:max [:succ [:zero]] [:succ V]]]]
      ['dictionary (function/arrow 'Container 'A 'Prop)]
      ['container 'Container] ['value 'A]]
     (function/app 'dictionary 'container 'value))}

   {:name 'set/membership
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A) 'A 'Prop))
    :value
    (function/lam
     [['A type-u]
      ['set (function/app (function/const* 'set/Set [U]) 'A)] ['value 'A]]
     (function/app 'set 'value))}

   {:name 'set/of
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/arrow 'A 'Prop)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam [['A type-u] ['predicate (function/arrow 'A 'Prop)]]
                  'predicate)}

   {:name 'set/preimage
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v]
      ['map (function/arrow 'A 'B)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u] ['B type-v] ['map (function/arrow 'A 'B)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]
      ['value 'A]]
     (function/app 'target (function/app 'map 'value)))}

   {:name 'set/range
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['map (function/arrow 'A 'B)]]
     (function/app (function/const* 'set/Set [V]) 'B))
    :value
    (function/lam
     [['A type-u] ['B type-v] ['map (function/arrow 'A 'B)] ['value 'B]]
     (proposition/existence
      [:succ U] 'A
      (function/lam
       [['source 'A]]
       (eq [:succ V] 'B (function/app 'map 'source) 'value))))}

   {:name 'set/image
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['map (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/app (function/const* 'set/Set [V]) 'B))
    :value
    (function/lam
     [['A type-u] ['B type-v] ['map (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['value 'B]]
     (proposition/existence
      [:succ U] 'A
      (function/lam
       [['input 'A]]
       (proposition/conjunction
        (function/app 'source 'input)
        (eq [:succ V] 'B (function/app 'map 'input) 'value)))))}

   {:name 'set/universal
    :universes ['u]
    :type
    (function/forall
     [['A type-u]] (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam [['A type-u] ['ignored 'A]] (proposition/truth))}

   {:name 'set/indexed-union
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['Index sort-v]
      ['family
       (function/arrow
        'Index (function/app (function/const* 'set/Set [U]) 'A))]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u] ['Index sort-v]
      ['family
       (function/arrow
        'Index (function/app (function/const* 'set/Set [U]) 'A))]
      ['value 'A]]
     (proposition/existence
      V 'Index
      (function/lam [['index 'Index]]
                    (function/app 'family 'index 'value))))}

   {:name 'set/indexed-intersection
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['Index sort-v]
      ['family
       (function/arrow
        'Index (function/app (function/const* 'set/Set [U]) 'A))]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u] ['Index sort-v]
      ['family
       (function/arrow
        'Index (function/app (function/const* 'set/Set [U]) 'A))]
      ['value 'A]]
     (function/forall
      [['index 'Index]] (function/app 'family 'index 'value)))}

   {:name 'subset/relation
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort]
        ['dictionary (function/arrow 'Container 'Container 'Prop)]
        ['left 'Container] ['right 'Container]]
       'Prop))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary (function/arrow 'Container 'Container 'Prop)]
      ['left 'Container] ['right 'Container]]
     (function/app 'dictionary 'left 'right))}

   {:name 'set/subset
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)
      'Prop))
    :value
    (function/lam
     [['A type-u]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/forall
      [['value 'A] ['evidence (function/app 'left 'value)]]
      (function/app 'right 'value)))}

   {:name 'collection/intersection
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort]
        ['dictionary (function/arrow 'Container 'Container 'Container)]
        ['left 'Container] ['right 'Container]]
       'Container))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary (function/arrow 'Container 'Container 'Container)]
      ['left 'Container] ['right 'Container]]
     (function/app 'dictionary 'left 'right))}

   {:name 'set/intersection
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [U]) 'A)]
      ['value 'A]]
     (proposition/conjunction (function/app 'left 'value)
                              (function/app 'right 'value)))}

   {:name 'collection/union
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort]
        ['dictionary (function/arrow 'Container 'Container 'Container)]
        ['left 'Container] ['right 'Container]]
       'Container))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary (function/arrow 'Container 'Container 'Container)]
      ['left 'Container] ['right 'Container]]
     (function/app 'dictionary 'left 'right))}

   {:name 'set/union
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [U]) 'A)]
      ['value 'A]]
     (proposition/disjunction (function/app 'left 'value)
                              (function/app 'right 'value)))}

   {:name 'set/nonempty
    :universes ['u]
    :type
    (function/forall
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     'Prop)
    :value
    (function/lam
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (proposition/existence [:succ U] 'A 'source))}

   {:name 'set/equal-on
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v]
      ['left (function/arrow 'A 'B)] ['right (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v]
      ['left (function/arrow 'A 'B)] ['right (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/forall
      [['value 'A :implicit] ['member (function/app 'source 'value)]]
      (eq [:succ V] 'B (function/app 'left 'value)
          (function/app 'right 'value))))}

   {:name 'set/maps-to
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     (function/forall
      [['value 'A :implicit] ['member (function/app 'source 'value)]]
      (function/app 'target (function/app 'mapping 'value))))}

   {:name 'set/injective-on
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/forall
      [['left 'A :implicit] ['left-member (function/app 'source 'left)]
       ['right 'A :implicit] ['right-member (function/app 'source 'right)]
       ['same-image
        (eq [:succ V] 'B (function/app 'mapping 'left)
            (function/app 'mapping 'right))]]
      (eq [:succ U] 'A 'left 'right)))}

   {:name 'set/surjective-on
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     (function/forall
      [['value 'B :implicit] ['target-member (function/app 'target 'value)]]
      (proposition/existence
       [:succ U] 'A
       (function/lam
        [['input 'A]]
        (proposition/conjunction
         (function/app 'source 'input)
         (eq [:succ V] 'B (function/app 'mapping 'input) 'value))))))}

   {:name 'set/bijective-on
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['target (function/app (function/const* 'set/Set [V]) 'B)]]
     (proposition/conjunction
      (function/app (function/const* 'set/maps-to [U V])
                    'A 'B 'mapping 'source 'target)
      (proposition/conjunction
       (function/app (function/const* 'set/injective-on [U V])
                     'A 'B 'mapping 'source)
       (function/app (function/const* 'set/surjective-on [U V])
                     'A 'B 'mapping 'source 'target))))}

   {:name 'set/left-inverse-on
    :universes ['u 'v]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     'Prop)
    :value
    (function/lam
     [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
      ['forward (function/arrow 'A 'B)]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/forall
      [['value 'A :implicit] ['member (function/app 'source 'value)]]
      (eq [:succ U] 'A
          (function/app 'backward (function/app 'forward 'value)) 'value)))}

   {:name 'set/image2
    :universes ['u 'v 'w]
    :type
    (function/forall
     [['A type-u] ['B type-v] ['C type-w]
      ['mapping (function/arrow 'A 'B 'C)]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [V]) 'B)]]
     (function/app (function/const* 'set/Set [W]) 'C))
    :value
    (function/lam
     [['A type-u] ['B type-v] ['C type-w]
      ['mapping (function/arrow 'A 'B 'C)]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [V]) 'B)]
      ['output 'C]]
     (proposition/existence
      [:succ U] 'A
      (function/lam
       [['left-input 'A]]
       (proposition/conjunction
        (function/app 'left 'left-input)
        (proposition/existence
         [:succ V] 'B
         (function/lam
          [['right-input 'B]]
          (proposition/conjunction
           (function/app 'right 'right-input)
           (eq [:succ W] 'C
               (function/app 'mapping 'left-input 'right-input)
               'output))))))))}

   {:name 'set/supremum
    :universes ['u]
    :type
    (function/forall
     [['A type-u]
      ['family
       (function/app
        (function/const* 'set/Set [U])
        (function/app (function/const* 'set/Set [U]) 'A))]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u]
      ['family
       (function/app
        (function/const* 'set/Set [U])
        (function/app (function/const* 'set/Set [U]) 'A))]
      ['value 'A]]
     (proposition/existence
      [:succ U]
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/lam
       [['source (function/app (function/const* 'set/Set [U]) 'A)]]
       (proposition/conjunction (function/app 'family 'source)
                                (function/app 'source 'value)))))}

   {:name 'set/infimum
    :universes ['u]
    :type
    (function/forall
     [['A type-u]
      ['family
       (function/app
        (function/const* 'set/Set [U])
        (function/app (function/const* 'set/Set [U]) 'A))]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u]
      ['family
       (function/app
        (function/const* 'set/Set [U])
        (function/app (function/const* 'set/Set [U]) 'A))]
      ['value 'A]]
     (function/forall
      [['source (function/app (function/const* 'set/Set [U]) 'A)]
       ['member (function/app 'family 'source)]]
      (function/app 'source 'value)))}

   {:name 'set/powerset
    :universes ['u]
    :type
    (function/forall
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/app
      (function/const* 'set/Set [U])
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['candidate (function/app (function/const* 'set/Set [U]) 'A)]]
     (function/forall
      [['value 'A] ['member (function/app 'candidate 'value)]]
      (function/app 'source 'value)))}

   {:name 'bool/not
    :universes []
    :type
    (function/arrow (function/const* 'data/Bool [])
                    (function/const* 'data/Bool []))
    :value
    (function/lam
     [['value (function/const* 'data/Bool [])]]
     (function/app
      (function/const* 'data/Bool.rec [[:succ [:zero]]])
      (function/lam [['ignored (function/const* 'data/Bool [])]]
                    (function/const* 'data/Bool []))
      (function/const* 'data/true [])
      (function/const* 'data/false [])
      'value))}

   {:name 'product/first
    :universes ['u 'v]
    :type
    (function/forall
     [['A sort-u] ['B sort-v]
      ['pair (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
     'A)
    :value
    (function/lam
     [['A sort-u] ['B sort-v]
      ['pair (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
     (function/app
      (function/const* 'data/Product.rec [U V U]) 'A 'B
      (function/lam
       [['ignored (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
       'A)
      (function/lam [['first 'A] ['second 'B]] 'first)
      'pair))}

   {:name 'product/second
    :universes ['u 'v]
    :type
    (function/forall
     [['A sort-u] ['B sort-v]
      ['pair (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
     'B)
    :value
    (function/lam
     [['A sort-u] ['B sort-v]
      ['pair (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
     (function/app
      (function/const* 'data/Product.rec [U V V]) 'A 'B
      (function/lam
       [['ignored (function/app (function/const* 'data/Product [U V]) 'A 'B)]]
       'B)
      (function/lam [['first 'A] ['second 'B]] 'second)
      'pair))}

   {:name 'nat/iterate
    :universes ['u]
    :type
    (function/forall
     [['A sort-u] ['step (function/arrow 'A 'A)]
      ['count (function/const* 'data/Nat [])]]
     (function/arrow 'A 'A))
    :value
    (function/lam
     [['A sort-u] ['step (function/arrow 'A 'A)]
      ['count (function/const* 'data/Nat [])]]
     (function/app
      (function/const* 'data/Nat.rec [[:imax U U]])
      (function/lam [['ignored (function/const* 'data/Nat [])]]
                    (function/arrow 'A 'A))
      (function/lam [['value 'A]] 'value)
      (function/lam
       [['predecessor (function/const* 'data/Nat [])]
        ['previous (function/arrow 'A 'A)] ['value 'A]]
       (function/app 'step (function/app 'previous 'value)))
      'count))}])

(def set-operator-specs
  [{:name 'collection/empty
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort] ['dictionary 'Container]]
       'Container))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary 'Container]]
     'dictionary)}

   {:name 'set/empty
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/app (function/const* 'set/Set [U]) 'A))
    :value
    (function/lam
     [['A type-u] ['value 'A]]
     (proposition/falsity))}

   {:name 'collection/singleton
    :universes ['u 'v]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ V]]]]
      (function/forall
       [['A type-u] ['Container container-sort]
        ['dictionary (function/arrow 'A 'Container)]
        ['value 'A]]
       'Container))
    :value
    (function/lam
     [['A type-u]
      ['Container [:sort [:max [:succ [:zero]] [:succ V]]]]
      ['dictionary (function/arrow 'A 'Container)]
      ['value 'A]]
     (function/app 'dictionary 'value))}

   {:name 'set/singleton
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow 'A
                     (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u] ['selected 'A] ['candidate 'A]]
     (eq [:succ U] 'A 'candidate 'selected))}

   {:name 'collection/complement
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort]
        ['dictionary (function/arrow 'Container 'Container)]
        ['source 'Container]]
       'Container))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary (function/arrow 'Container 'Container)]
      ['source 'Container]]
     (function/app 'dictionary 'source))}

   {:name 'set/complement
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['value 'A]]
     (proposition/negation (function/app 'source 'value)))}

   {:name 'collection/difference
    :universes ['u]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ U]]]]
      (function/forall
       [['Container container-sort]
        ['dictionary (function/arrow 'Container 'Container 'Container)]
        ['left 'Container] ['right 'Container]]
       'Container))
    :value
    (function/lam
     [['Container [:sort [:max [:succ [:zero]] [:succ U]]]]
      ['dictionary (function/arrow 'Container 'Container 'Container)]
      ['left 'Container] ['right 'Container]]
     (function/app 'dictionary 'left 'right))}

   {:name 'set/difference
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u]
      ['left (function/app (function/const* 'set/Set [U]) 'A)]
      ['right (function/app (function/const* 'set/Set [U]) 'A)]
      ['value 'A]]
     (proposition/conjunction
      (function/app 'left 'value)
      (proposition/negation (function/app 'right 'value))))}

   {:name 'collection/insert
    :universes ['u 'v]
    :type
    (let [container-sort [:sort [:max [:succ [:zero]] [:succ V]]]]
      (function/forall
       [['A type-u] ['Container container-sort]
        ['dictionary (function/arrow 'A 'Container 'Container)]
        ['value 'A] ['source 'Container]]
       'Container))
    :value
    (function/lam
     [['A type-u]
      ['Container [:sort [:max [:succ [:zero]] [:succ V]]]]
      ['dictionary (function/arrow 'A 'Container 'Container)]
      ['value 'A] ['source 'Container]]
     (function/app 'dictionary 'value 'source))}

   {:name 'set/insert
    :universes ['u]
    :type
    (function/forall
     [['A type-u]]
     (function/arrow
      'A
      (function/app (function/const* 'set/Set [U]) 'A)
      (function/app (function/const* 'set/Set [U]) 'A)))
    :value
    (function/lam
     [['A type-u] ['selected 'A]
      ['source (function/app (function/const* 'set/Set [U]) 'A)]
      ['candidate 'A]]
     (proposition/disjunction
      (eq [:succ U] 'A 'candidate 'selected)
      (function/app 'source 'candidate)))}])

(def set-structural-specs
  (let [product-type
        (fn [a b]
          (function/app
           (function/const* 'data/Product [[:succ U] [:succ V]]) a b))
        first-of
        (fn [a b pair]
          (function/app
           (function/const* 'product/first [[:succ U] [:succ V]])
           a b pair))
        second-of
        (fn [a b pair]
          (function/app
           (function/const* 'product/second [[:succ U] [:succ V]])
           a b pair))]
    [{:name 'collection/set-product
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['Left [:sort [:max [:succ [:zero]] [:succ U]]]]
        ['Right [:sort [:max [:succ [:zero]] [:succ V]]]]
        ['Output [:sort [:max [:succ [:zero]] [:succ W]]]]
        ['dictionary (function/arrow 'Left 'Right 'Output)]
        ['left 'Left] ['right 'Right]]
       'Output)
      :value
      (function/lam
       [['Left [:sort [:max [:succ [:zero]] [:succ U]]]]
        ['Right [:sort [:max [:succ [:zero]] [:succ V]]]]
        ['Output [:sort [:max [:succ [:zero]] [:succ W]]]]
        ['dictionary (function/arrow 'Left 'Right 'Output)]
        ['left 'Left] ['right 'Right]]
       (function/app 'dictionary 'left 'right))}

     {:name 'set/product
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v]]
       (function/arrow
        (function/app (function/const* 'set/Set [U]) 'A)
        (function/app (function/const* 'set/Set [V]) 'B)
        (function/app (function/const* 'set/Set [[:max U V]])
                      (product-type 'A 'B))))
      :value
      (function/lam
       [['A type-u] ['B type-v]
        ['left (function/app (function/const* 'set/Set [U]) 'A)]
        ['right (function/app (function/const* 'set/Set [V]) 'B)]
        ['pair (product-type 'A 'B)]]
       (proposition/conjunction
        (function/app 'left (first-of 'A 'B 'pair))
        (function/app 'right (second-of 'A 'B 'pair))))}

     {:name 'set/pi
      :universes ['u 'v]
      :type
      (let [family-type (function/arrow 'I type-v)
            dependent-type
            (function/forall [['index 'I]] (function/app 'A 'index))]
        (function/forall
         [['I type-u] ['A family-type]
          ['source (function/app (function/const* 'set/Set [U]) 'I)]
          ['target
           (function/forall
            [['index 'I]]
            (function/app (function/const* 'set/Set [V])
                          (function/app 'A 'index)))]]
         (function/app (function/const* 'set/Set [[:max U V]])
                       dependent-type)))
      :value
      (function/lam
       [['I type-u] ['A (function/arrow 'I type-v)]
        ['source (function/app (function/const* 'set/Set [U]) 'I)]
        ['target
         (function/forall
          [['index 'I]]
          (function/app (function/const* 'set/Set [V])
                        (function/app 'A 'index)))]
        ['candidate
         (function/forall [['index 'I]] (function/app 'A 'index))]]
       (function/forall
        [['index 'I] ['member (function/app 'source 'index)]]
        (function/app 'target 'index (function/app 'candidate 'index))))}

     {:name 'set/subsingleton
      :universes ['u]
      :type
      (function/forall
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       'Prop)
      :value
      (function/lam
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       (function/forall
        [['left 'A :implicit] ['left-member (function/app 'source 'left)]
         ['right 'A :implicit] ['right-member (function/app 'source 'right)]]
        (eq [:succ U] 'A 'left 'right)))}

     {:name 'set/nontrivial
      :universes ['u]
      :type
      (function/forall
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       'Prop)
      :value
      (function/lam
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       (proposition/existence
        [:succ U] 'A
        (function/lam
         [['left 'A]]
         (proposition/conjunction
          (function/app 'source 'left)
          (proposition/existence
           [:succ U] 'A
           (function/lam
            [['right 'A]]
            (proposition/conjunction
             (function/app 'source 'right)
             (proposition/negation
              (eq [:succ U] 'A 'left 'right)))))))))}

     {:name 'set/pairwise
      :universes ['u]
      :type
      (function/forall
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['relation (function/arrow 'A 'A 'Prop)]]
       'Prop)
      :value
      (function/lam
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['relation (function/arrow 'A 'A 'Prop)]]
       (function/forall
        [['left 'A :implicit] ['left-member (function/app 'source 'left)]
         ['right 'A :implicit] ['right-member (function/app 'source 'right)]
         ['distinct
          (proposition/negation (eq [:succ U] 'A 'left 'right))]]
        (function/app 'relation 'left 'right)))}

     {:name 'set/graph-on
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       (function/app (function/const* 'set/Set [[:max U V]])
                     (product-type 'A 'B)))
      :value
      (function/lam
       [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['output (product-type 'A 'B)]]
       (proposition/existence
        [:succ U] 'A
        (function/lam
         [['input 'A]]
         (proposition/conjunction
          (function/app 'source 'input)
          (eq [:succ [:max U V]] (product-type 'A 'B)
              (function/app
               (function/const* 'data/pair [[:succ U] [:succ V]])
               'A 'B 'input (function/app 'mapping 'input))
              'output)))))}

     {:name 'set/right-inverse-on
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
        ['forward (function/arrow 'A 'B)]
        ['target (function/app (function/const* 'set/Set [V]) 'B)]]
       'Prop)
      :value
      (function/lam
       [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
        ['forward (function/arrow 'A 'B)]
        ['target (function/app (function/const* 'set/Set [V]) 'B)]]
       (function/forall
        [['value 'B :implicit] ['member (function/app 'target 'value)]]
        (eq [:succ V] 'B
            (function/app 'forward (function/app 'backward 'value))
            'value)))}

     {:name 'set/inverse-on
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
        ['forward (function/arrow 'A 'B)]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['target (function/app (function/const* 'set/Set [V]) 'B)]]
       'Prop)
      :value
      (function/lam
       [['A type-u] ['B type-v] ['backward (function/arrow 'B 'A)]
        ['forward (function/arrow 'A 'B)]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['target (function/app (function/const* 'set/Set [V]) 'B)]]
       (proposition/conjunction
        (function/app (function/const* 'set/left-inverse-on [U V])
                      'A 'B 'backward 'forward 'source)
        (function/app (function/const* 'set/right-inverse-on [U V])
                      'A 'B 'backward 'forward 'target)))}

     {:name 'function/fixed-points
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['mapping (function/arrow 'A 'A)]]
       (function/app (function/const* 'set/Set [U]) 'A))
      :value
      (function/lam
       [['A type-u] ['mapping (function/arrow 'A 'A)] ['value 'A]]
       (eq [:succ U] 'A (function/app 'mapping 'value) 'value))}

     {:name 'function/injective2
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['A sort-u] ['B sort-v] ['C sort-w]
        ['mapping (function/arrow 'A 'B 'C)]]
       'Prop)
      :value
      (function/lam
       [['A sort-u] ['B sort-v] ['C sort-w]
        ['mapping (function/arrow 'A 'B 'C)]]
       (function/forall
        [['left-a 'A] ['left-b 'B] ['right-a 'A] ['right-b 'B]
         ['same
          (eq W 'C (function/app 'mapping 'left-a 'left-b)
              (function/app 'mapping 'right-a 'right-b))]]
        (proposition/conjunction
         (eq U 'A 'left-a 'right-a)
         (eq V 'B 'left-b 'right-b))))}

     {:name 'set/diagonal
      :universes ['u]
      :type
      (function/forall
       [['A type-u]]
       (function/app (function/const* 'set/Set [U])
                     (function/app
                      (function/const* 'data/Product
                                       [[:succ U] [:succ U]])
                      'A 'A)))
      :value
      (function/lam
       [['A type-u]
        ['pair
         (function/app
          (function/const* 'data/Product [[:succ U] [:succ U]]) 'A 'A)]]
       (eq [:succ U] 'A
           (function/app
            (function/const* 'product/first [[:succ U] [:succ U]])
            'A 'A 'pair)
           (function/app
            (function/const* 'product/second [[:succ U] [:succ U]])
            'A 'A 'pair)))}

     {:name 'set/off-diagonal
      :universes ['u]
      :type
      (function/forall
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]]
       (function/app (function/const* 'set/Set [U])
                     (function/app
                      (function/const* 'data/Product
                                       [[:succ U] [:succ U]])
                      'A 'A)))
      :value
      (function/lam
       [['A type-u]
        ['source (function/app (function/const* 'set/Set [U]) 'A)]
        ['pair
         (function/app
          (function/const* 'data/Product [[:succ U] [:succ U]]) 'A 'A)]]
       (let [first
             (function/app
              (function/const* 'product/first [[:succ U] [:succ U]])
              'A 'A 'pair)
             second
             (function/app
              (function/const* 'product/second [[:succ U] [:succ U]])
              'A 'A 'pair)]
         (proposition/conjunction
          (function/app 'source first)
          (proposition/conjunction
           (function/app 'source second)
           (proposition/negation (eq [:succ U] 'A first second))))))}]))

(def data-combinator-specs
  (let [option-of
        (fn [level carrier]
          (function/app (function/const* 'data/Option [[:succ level]])
                        carrier))
        product-of
        (fn [left-level right-level left right]
          (function/app
           (function/const* 'data/Product
                            [[:succ left-level] [:succ right-level]])
           left right))
        sum-of
        (fn [left-level right-level left right]
          (function/app
           (function/const* 'data/Sum
                            [[:succ left-level] [:succ right-level]])
           left right))]
    [{:name 'option/map
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
        ['source (option-of U 'A)]]
       (option-of V 'B))
      :value
      (function/lam
       [['A type-u] ['B type-v] ['mapping (function/arrow 'A 'B)]
        ['source (option-of U 'A)]]
       (function/app
        (function/const* 'data/Option.rec [[:succ U] [:succ V]])
        'A
        (function/lam [['ignored (option-of U 'A)]] (option-of V 'B))
        (function/app (function/const* 'data/none [[:succ V]]) 'B)
        (function/lam
         [['value 'A]]
         (function/app (function/const* 'data/some [[:succ V]])
                       'B (function/app 'mapping 'value)))
        'source))}

     {:name 'option/map2
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['C type-w]
        ['mapping (function/arrow 'A 'B 'C)]
        ['left (option-of U 'A)] ['right (option-of V 'B)]]
       (option-of W 'C))
      :value
      (function/lam
       [['A type-u] ['B type-v] ['C type-w]
        ['mapping (function/arrow 'A 'B 'C)]
        ['left (option-of U 'A)] ['right (option-of V 'B)]]
       (function/app
        (function/const* 'data/Option.rec [[:succ U] [:succ W]])
        'A
        (function/lam [['ignored (option-of U 'A)]] (option-of W 'C))
        (function/app (function/const* 'data/none [[:succ W]]) 'C)
        (function/lam
         [['left-value 'A]]
         (function/app
          (function/const* 'data/Option.rec [[:succ V] [:succ W]])
          'B
          (function/lam [['ignored (option-of V 'B)]] (option-of W 'C))
          (function/app (function/const* 'data/none [[:succ W]]) 'C)
          (function/lam
           [['right-value 'B]]
           (function/app
            (function/const* 'data/some [[:succ W]]) 'C
            (function/app 'mapping 'left-value 'right-value)))
          'right))
        'left))}

     {:name 'option/eliminate
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['fallback 'B]
        ['present (function/arrow 'A 'B)] ['source (option-of U 'A)]]
       'B)
      :value
      (function/lam
       [['A type-u] ['B type-v] ['fallback 'B]
        ['present (function/arrow 'A 'B)] ['source (option-of U 'A)]]
       (function/app
        (function/const* 'data/Option.rec [[:succ U] [:succ V]])
        'A (function/lam [['ignored (option-of U 'A)]] 'B)
        'fallback 'present 'source))}

     {:name 'product/map
      :universes ['u 'v 'w 'x]
      :type
      (function/forall
       [['A type-u] ['A2 type-v] ['B type-w] ['B2 type-x]
        ['left-map (function/arrow 'A 'A2)]
        ['right-map (function/arrow 'B 'B2)]
        ['source (product-of U W 'A 'B)]]
       (product-of V X 'A2 'B2))
      :value
      (function/lam
       [['A type-u] ['A2 type-v] ['B type-w] ['B2 type-x]
        ['left-map (function/arrow 'A 'A2)]
        ['right-map (function/arrow 'B 'B2)]
        ['source (product-of U W 'A 'B)]]
       (function/app
        (function/const* 'data/Product.rec
                         [[:succ U] [:succ W] [:succ [:max V X]]])
        'A 'B
        (function/lam
         [['ignored (product-of U W 'A 'B)]] (product-of V X 'A2 'B2))
        (function/lam
         [['left 'A] ['right 'B]]
         (function/app
          (function/const* 'data/pair [[:succ V] [:succ X]])
          'A2 'B2 (function/app 'left-map 'left)
          (function/app 'right-map 'right)))
        'source))}

     {:name 'product/swap
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['source (product-of U V 'A 'B)]]
       (product-of V U 'B 'A))
      :value
      (function/lam
       [['A type-u] ['B type-v] ['source (product-of U V 'A 'B)]]
       (function/app
        (function/const* 'data/Product.rec
                         [[:succ U] [:succ V] [:succ [:max U V]]])
        'A 'B
        (function/lam
         [['ignored (product-of U V 'A 'B)]] (product-of V U 'B 'A))
        (function/lam
         [['left 'A] ['right 'B]]
         (function/app
          (function/const* 'data/pair [[:succ V] [:succ U]])
          'B 'A 'right 'left))
        'source))}

     {:name 'sum/eliminate
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['C sort-w]
        ['left-case (function/arrow 'A 'C)]
        ['right-case (function/arrow 'B 'C)]
        ['source (sum-of U V 'A 'B)]]
       'C)
      :value
      (function/lam
       [['A type-u] ['B type-v] ['C sort-w]
        ['left-case (function/arrow 'A 'C)]
        ['right-case (function/arrow 'B 'C)]
        ['source (sum-of U V 'A 'B)]]
       (function/app
        (function/const* 'data/Sum.rec [[:succ U] [:succ V] W])
        'A 'B (function/lam [['ignored (sum-of U V 'A 'B)]] 'C)
        'left-case 'right-case 'source))}

     {:name 'sum/map
      :universes ['u 'v 'w 'x]
      :type
      (function/forall
       [['A type-u] ['A2 type-v] ['B type-w] ['B2 type-x]
        ['left-map (function/arrow 'A 'A2)]
        ['right-map (function/arrow 'B 'B2)]
        ['source (sum-of U W 'A 'B)]]
       (sum-of V X 'A2 'B2))
      :value
      (function/lam
       [['A type-u] ['A2 type-v] ['B type-w] ['B2 type-x]
        ['left-map (function/arrow 'A 'A2)]
        ['right-map (function/arrow 'B 'B2)]
        ['source (sum-of U W 'A 'B)]]
       (function/app
        (function/const* 'data/Sum.rec
                         [[:succ U] [:succ W] [:succ [:max V X]]])
        'A 'B
        (function/lam [['ignored (sum-of U W 'A 'B)]]
                      (sum-of V X 'A2 'B2))
        (function/lam
         [['value 'A]]
         (function/app (function/const* 'data/left [[:succ V] [:succ X]])
                       'A2 'B2 (function/app 'left-map 'value)))
        (function/lam
         [['value 'B]]
         (function/app (function/const* 'data/right [[:succ V] [:succ X]])
                       'A2 'B2 (function/app 'right-map 'value)))
        'source))}

     {:name 'function/evaluate
      :universes ['u 'v]
      :type
      (function/forall
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['value 'A] ['mapping (function/forall
                              [['input 'A]] (function/app 'B 'input))]]
       (function/app 'B 'value))
      :value
      (function/lam
       [['A sort-u] ['B (function/arrow 'A [:sort V])]
        ['value 'A] ['mapping (function/forall
                              [['input 'A]] (function/app 'B 'input))]]
       (function/app 'mapping 'value))}

     {:name 'function/swap
      :universes ['u 'v 'w]
      :type
      (let [family
            (function/forall
             [['left 'A] ['right 'B]] [:sort W])]
        (function/forall
         [['A sort-u] ['B sort-v] ['C family]
          ['mapping
           (function/forall
            [['left 'A] ['right 'B]]
            (function/app 'C 'left 'right))]]
         (function/forall
          [['right 'B] ['left 'A]]
          (function/app 'C 'left 'right))))
      :value
      (function/lam
       [['A sort-u] ['B sort-v]
        ['C (function/forall [['left 'A] ['right 'B]] [:sort W])]
        ['mapping
         (function/forall
          [['left 'A] ['right 'B]] (function/app 'C 'left 'right))]
        ['right 'B] ['left 'A]]
       (function/app 'mapping 'left 'right))}

     {:name 'function/uncurry
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['A type-u] ['B type-v] ['C sort-w]
        ['mapping (function/arrow 'A 'B 'C)]
        ['source (product-of U V 'A 'B)]]
       'C)
      :value
      (function/lam
       [['A type-u] ['B type-v] ['C sort-w]
        ['mapping (function/arrow 'A 'B 'C)]
        ['source (product-of U V 'A 'B)]]
       (function/app
        (function/const* 'data/Product.rec [[:succ U] [:succ V] W])
        'A 'B (function/lam [['ignored (product-of U V 'A 'B)]] 'C)
        'mapping 'source))}

     {:name 'bool/and
      :universes []
      :type
      (function/arrow (function/const* 'data/Bool [])
                      (function/const* 'data/Bool [])
                      (function/const* 'data/Bool []))
      :value
      (function/lam
       [['left (function/const* 'data/Bool [])]
        ['right (function/const* 'data/Bool [])]]
       (function/app
        (function/const* 'data/Bool.rec [[:succ [:zero]]])
        (function/lam [['ignored (function/const* 'data/Bool [])]]
                      (function/const* 'data/Bool []))
        (function/const* 'data/false []) 'right 'left))}

     {:name 'bool/or
      :universes []
      :type
      (function/arrow (function/const* 'data/Bool [])
                      (function/const* 'data/Bool [])
                      (function/const* 'data/Bool []))
      :value
      (function/lam
       [['left (function/const* 'data/Bool [])]
        ['right (function/const* 'data/Bool [])]]
       (function/app
        (function/const* 'data/Bool.rec [[:succ [:zero]]])
        (function/lam [['ignored (function/const* 'data/Bool [])]]
                      (function/const* 'data/Bool []))
        'right (function/const* 'data/true []) 'left))}]))

(def inductive-membership-specs
  (let [list-of
        (fn [element]
          (function/app (function/const* 'data/List [[:succ U]]) element))
        option-of
        (fn [element]
          (function/app (function/const* 'data/Option [[:succ U]]) element))]
    [{:name 'list/membership
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['source (list-of 'A)] ['value 'A]] 'Prop)
      :value
      (function/lam
       [['A type-u] ['source (list-of 'A)]]
       (function/app
        (function/const* 'data/List.rec [[:succ U] [:succ U]])
        'A
        (function/lam
         [['ignored (list-of 'A)]] (function/arrow 'A 'Prop))
        (function/lam [['value 'A]] (proposition/falsity))
        (function/lam
         [['head 'A] ['tail (list-of 'A)]
          ['tail-membership (function/arrow 'A 'Prop)] ['value 'A]]
         (proposition/disjunction
          (eq [:succ U] 'A 'value 'head)
          (function/app 'tail-membership 'value)))
        'source))}

     {:name 'option/membership
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['source (option-of 'A)] ['value 'A]] 'Prop)
      :value
      (function/lam
       [['A type-u] ['source (option-of 'A)]]
       (function/app
        (function/const* 'data/Option.rec [[:succ U] [:succ U]])
        'A
        (function/lam
         [['ignored (option-of 'A)]] (function/arrow 'A 'Prop))
        (function/lam [['value 'A]] (proposition/falsity))
        (function/lam
         [['candidate 'A] ['value 'A]]
         (eq [:succ U] 'A 'value 'candidate))
        'source))}]))

(def set-function-specs
  (let [set-of
        (fn [level element]
          (function/app (function/const* 'set/Set [level]) element))
        elem-of
        (fn [level element source]
          (function/app (function/const* 'set/element-type [level])
                        element source))]
    [{:name 'set/ite
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['test (set-of U 'A)]
        ['then-set (set-of U 'A)] ['else-set (set-of U 'A)]]
       (set-of U 'A))
      :value
      (function/lam
       [['A type-u] ['test (set-of U 'A)]
        ['then-set (set-of U 'A)] ['else-set (set-of U 'A)] ['value 'A]]
       (proposition/disjunction
        (proposition/conjunction (function/app 'then-set 'value)
                                 (function/app 'test 'value))
        (proposition/conjunction
         (function/app 'else-set 'value)
         (proposition/negation (function/app 'test 'value))))) }

     {:name 'set/restrict
      :universes ['u 'v]
      :type
      (function/forall
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (set-of U 'A)]
        ['mapping (function/forall [['value 'A]] (function/app 'B 'value))]
        ['value (elem-of U 'A 'source)]]
       (function/app
        'B (function/app (function/const* 'subtype/value [[:succ U]])
                         'A 'source 'value)))
      :value
      (function/lam
       [['A type-u] ['B (function/arrow 'A type-v)]
        ['source (set-of U 'A)]
        ['mapping (function/forall [['value 'A]] (function/app 'B 'value))]
        ['value (elem-of U 'A 'source)]]
       (function/app
        'mapping
        (function/app (function/const* 'subtype/value [[:succ U]])
                      'A 'source 'value)))}

     {:name 'set/restrict-preimage
      :universes ['u 'v]
      :type
      (let [preimage
            (function/app (function/const* 'set/preimage [U V])
                          'A 'B 'mapping 'target)]
        (function/forall
         [['A type-u] ['B type-v] ['target (set-of V 'B)]
          ['mapping (function/arrow 'A 'B)]
          ['source (elem-of U 'A preimage)]]
         (elem-of V 'B 'target)))
      :value
      (let [preimage
            (function/app (function/const* 'set/preimage [U V])
                          'A 'B 'mapping 'target)
            value
            (function/app (function/const* 'subtype/value [[:succ U]])
                          'A preimage 'source)]
        (function/lam
         [['A type-u] ['B type-v] ['target (set-of V 'B)]
          ['mapping (function/arrow 'A 'B)]
          ['source (elem-of U 'A preimage)]]
         (function/app
          (function/const* 'data/subtype [[:succ V]])
          'B 'target (function/app 'mapping value)
          (function/app (function/const* 'subtype/property [[:succ U]])
                        'A preimage 'source))))}

     {:name 'set/seq
      :universes ['u 'v]
      :type
      (let [mapping-type (function/arrow 'A 'B)]
        (function/forall
         [['A type-u] ['B type-v]
          ['mappings (set-of [:max U V] mapping-type)]
          ['inputs (set-of U 'A)]]
         (set-of V 'B)))
      :value
      (function/lam
       [['A type-u] ['B type-v]
        ['mappings (set-of [:max U V] (function/arrow 'A 'B))]
        ['inputs (set-of U 'A)]]
       (function/app
        (function/const* 'set/image2 [[:max U V] U V])
        (function/arrow 'A 'B) 'A 'B
        (function/lam
         [['mapping (function/arrow 'A 'B)] ['value 'A]]
         (function/app 'mapping 'value))
        'mappings 'inputs))}

     {:name 'function/pi-map
      :universes ['u 'v 'w]
      :type
      (function/forall
       [['I sort-u] ['A (function/arrow 'I [:sort V])]
        ['B (function/arrow 'I [:sort W])]
        ['mapping (function/forall
                   [['index 'I]]
                   (function/arrow (function/app 'A 'index)
                                   (function/app 'B 'index)))]
        ['source (function/forall
                  [['index 'I]] (function/app 'A 'index))]
        ['index 'I]]
       (function/app 'B 'index))
      :value
      (function/lam
       [['I sort-u] ['A (function/arrow 'I [:sort V])]
        ['B (function/arrow 'I [:sort W])]
        ['mapping (function/forall
                   [['index 'I]]
                   (function/arrow (function/app 'A 'index)
                                   (function/app 'B 'index)))]
        ['source (function/forall
                  [['index 'I]] (function/app 'A 'index))]
        ['index 'I]]
       (function/app 'mapping 'index (function/app 'source 'index)))}]))

(def finite-set-specs
  (let [set-of
        (fn [element]
          (function/app (function/const* 'set/Set [U]) element))
        list-of
        (fn [element]
          (function/app (function/const* 'data/List [[:succ U]]) element))]
    [{:name 'set/finite
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['source (set-of 'A)]] 'Prop)
      :value
      (function/lam
       [['A type-u] ['source (set-of 'A)]]
       (proposition/existence
        [:succ U] (list-of 'A)
        (function/lam
         [['enumeration (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (function/app 'source 'value)]]
          (function/app (function/const* 'list/membership [U])
                        'A 'enumeration 'value)))))}

     {:name 'set/infinite
      :universes ['u]
      :type
      (function/forall
       [['A type-u] ['source (set-of 'A)]] 'Prop)
      :value
      (function/lam
       [['A type-u] ['source (set-of 'A)]]
       (proposition/negation
        (function/app (function/const* 'set/finite [U]) 'A 'source)))}]))

(def constant-aliases
  {"id" 'function/identity
   "Function.comp" 'function/compose
   "Function.LeftInverse" 'function/left-inverse
   "Function.RightInverse" 'function/right-inverse
   "Nonempty" 'proposition/nonempty
   "IsEmpty" 'proposition/is-empty
   "Bool" 'data/Bool
   "Bool.false" 'data/false
   "Bool.true" 'data/true
   "Bool.rec" 'data/Bool.rec
   "Nat" 'data/Nat
   "Nat.zero" 'data/zero
   "Nat.succ" 'data/succ
   "Nat.rec" 'data/Nat.rec
   "Prod" 'data/Product
   "Prod.mk" 'data/pair
   "Prod.rec" 'data/Product.rec
   "Sum" 'data/Sum
   "Sum.inl" 'data/left
   "Sum.inr" 'data/right
   "Sum.rec" 'data/Sum.rec
   "List" 'data/List
   "List.nil" 'data/nil
   "List.cons" 'data/cons
   "List.rec" 'data/List.rec})

(def combinator-constant-aliases
  {"Xor" 'proposition/xor
   "Symmetric" 'relation/symmetric
   "Function.Commute" 'function/commute
   "Function.Semiconj" 'function/semiconjugate
   "Function.IsFixedPt" 'function/fixed-point
   "Function.onFun" 'function/on-results
   "Nonempty.intro" 'proposition/nonempty-intro})

(def collection-constant-aliases
  {"Bool.not" 'bool/not
   "Nat.iterate" 'nat/iterate
   "Prod.fst" 'product/first
   "Prod.snd" 'product/second
   "List.length" 'list/length
   "List.map" 'list/map
   "Option" 'data/Option
   "Option.none" 'data/none
   "Option.some" 'data/some
   "Option.rec" 'data/Option.rec
   "Set" 'set/Set
   "Membership.mem" 'membership/member
   "Set.instMembership" 'set/membership
   "setOf" 'set/of
   "Set.preimage" 'set/preimage
   "Set.range" 'set/range
   "Set.image" 'set/image
   "Set.univ" 'set/universal
   "Set.iUnion" 'set/indexed-union
   "Set.iInter" 'set/indexed-intersection
   "HasSubset.Subset" 'subset/relation
   "Set.instHasSubset" 'set/subset
   "Inter.inter" 'collection/intersection
   "Set.instInter" 'set/intersection
   "Union.union" 'collection/union
   "Set.instUnion" 'set/union})

(def expanded-set-constant-aliases
  {"Set.Nonempty" 'set/nonempty
   "Set.EqOn" 'set/equal-on
   "Set.MapsTo" 'set/maps-to
   "Set.InjOn" 'set/injective-on
   "Set.SurjOn" 'set/surjective-on
   "Set.BijOn" 'set/bijective-on
   "Set.LeftInvOn" 'set/left-inverse-on
   "Set.image2" 'set/image2
   "Set.sUnion" 'set/supremum
   "Set.sInter" 'set/infimum
   "Set.powerset" 'set/powerset})

(def set-operator-constant-aliases
  {"EmptyCollection.emptyCollection" 'collection/empty
   "Set.instEmptyCollection" 'set/empty
   "Singleton.singleton" 'collection/singleton
   "Set.instSingletonSet" 'set/singleton
   "Compl.compl" 'collection/complement
   "Set.instCompl" 'set/complement
   "SDiff.sdiff" 'collection/difference
   "Set.instSDiff" 'set/difference
   "Insert.insert" 'collection/insert
   "Set.instInsert" 'set/insert})

(def set-structural-constant-aliases
  {"SProd.sprod" 'collection/set-product
   "Set.instSProd" 'set/product
   "Set.pi" 'set/pi
   "Set.Subsingleton" 'set/subsingleton
   "Set.Nontrivial" 'set/nontrivial
   "Set.Pairwise" 'set/pairwise
   "Set.graphOn" 'set/graph-on
   "Set.RightInvOn" 'set/right-inverse-on
   "Set.InvOn" 'set/inverse-on
   "Function.fixedPoints" 'function/fixed-points
   "Function.Injective2" 'function/injective2
   "Set.diagonal" 'set/diagonal
   "Set.offDiag" 'set/off-diagonal})

(def data-combinator-constant-aliases
  {"Option.map" 'option/map
   "Option.map₂" 'option/map2
   "Option.elim'" 'option/eliminate
   "Prod.map" 'product/map
   "Prod.swap" 'product/swap
   "Sum.elim" 'sum/eliminate
   "Sum.map" 'sum/map
   "Function.eval" 'function/evaluate
   "Function.swap" 'function/swap
   "Function.uncurry" 'function/uncurry
   "Bool.and" 'bool/and
   "Bool.or" 'bool/or})

(def subtype-constant-aliases
  {"Subtype" 'data/Subtype
   "Subtype.mk" 'data/subtype
   "Subtype.val" 'subtype/value
   "Subtype.property" 'subtype/property
   "Set.Elem" 'set/element-type})

(def inductive-membership-constant-aliases
  {"List.instMembership" 'list/membership
   "Option.instMembership" 'option/membership})

(def dependent-sum-constant-aliases
  {"Sigma" 'data/Sigma
   "Sigma.mk" 'data/sigma
   "Sigma.fst" 'sigma/first
   "Sigma.snd" 'sigma/second
   "PSigma" 'data/PSigma
   "PSigma.mk" 'data/psigma
   "PSigma.fst" 'psigma/first
   "PSigma.snd" 'psigma/second})

(def set-function-constant-aliases
  {"Set.ite" 'set/ite
   "Set.restrict" 'set/restrict
   "Set.restrictPreimage" 'set/restrict-preimage
   "Set.seq" 'set/seq
   "Pi.map" 'function/pi-map})

(def finite-set-constant-aliases
  {"Set.Finite" 'set/finite
   "Set.Infinite" 'set/infinite})

(def collection-expanded-constant-aliases
  "V1.15 concept map. Lean's inductive universe parameter `u` denotes element
  type `Type u`; Rainbow's data blocks parameterize directly by the element's
  sort level, so these mappings declare the one-successor translation."
  (merge
   constant-aliases combinator-constant-aliases collection-constant-aliases
   (into {}
         (map (fn [[foreign-name native-alias]]
                [foreign-name
                 {:native/alias native-alias
                  :native/level-transform :successor}]))
         {"Prod" 'data/Product
          "Prod.mk" 'data/pair
          "Prod.rec" 'data/Product.rec
          "Prod.fst" 'product/first
          "Prod.snd" 'product/second
          "Sum" 'data/Sum
          "Sum.inl" 'data/left
          "Sum.inr" 'data/right
          "Sum.rec" 'data/Sum.rec
          "List" 'data/List
          "List.nil" 'data/nil
          "List.cons" 'data/cons
          "List.rec" 'data/List.rec
          "List.length" 'list/length
          "List.map" 'list/map
          "Option" 'data/Option
          "Option.none" 'data/none
          "Option.some" 'data/some
          "Option.rec" 'data/Option.rec})))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Prelude concept failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn- extend-specs [checked-environment specs]
  (reduce
   (fn [environment spec]
     (let [type (elaborate! environment (:type spec))
           value (elaborate! environment (:value spec))
           added
           (kernel/add-declaration
            environment
            {:rainbow/kind :definition
             :rainbow/aliases #{(:name spec)}
             :rainbow/universes (:universes spec)
             :rainbow/type type :rainbow/value value
             :rainbow/transparency :reducible
             :rainbow/dependencies
             (into (term/constants type) (term/constants value))
             :rainbow/provenance
             {:origin :native :producer :corpus-measured-prelude-concept}
             :rainbow/schema-version 1})]
       (when-not (= :accepted (:status added))
         (throw (ex-info "Prelude concept declaration rejected"
                         {:name (:name spec) :result added})))
       (:environment added)))
   checked-environment specs))

(def expanded-set-spec-names
  '#{set/nonempty set/equal-on set/maps-to set/injective-on
     set/surjective-on set/bijective-on set/left-inverse-on set/image2
     set/supremum set/infimum set/powerset})

(defn extend-set-relations
  "Adds the V1.22 predicate-set relation layer to a checkpoint that already
  contains the original collection prelude."
  [checked-environment]
  (extend-specs checked-environment
                (filterv #(contains? expanded-set-spec-names (:name %))
                         collection-specs)))

(defn extend-set-operators
  "Adds the corpus-selected empty, singleton, complement, difference, and
  insert representations to an environment containing the collection prelude."
  [checked-environment]
  (extend-specs checked-environment set-operator-specs))

(defn extend-set-structural
  "Adds the measured Set product, dependent-function, cardinality-predicate,
  graph, inverse, fixed-point, and pair-relation representation layer."
  [checked-environment]
  (extend-specs checked-environment set-structural-specs))

(defn extend-data-combinators
  "Adds measured Product, Option, Sum, Function, and Bool combinators through
  ordinary reducible definitions over Rainbow's inductive proof data."
  [checked-environment]
  (extend-specs checked-environment data-combinator-specs))

(defn extend-subtypes
  "Adds the dependent Subtype block, its computed projections, and Set.Elem."
  [checked-environment]
  (let [added (kernel/add-inductive-block checked-environment subtype-spec)]
    (when-not (= :accepted (:status added))
      (throw (ex-info "Dependent Subtype proof-data block rejected"
                      {:result added})))
    (extend-specs (:environment added) subtype-definition-specs)))

(defn extend-inductive-memberships
  "Adds recursor-defined List and Option membership dictionaries."
  [checked-environment]
  (extend-specs checked-environment inductive-membership-specs))

(defn extend-dependent-sums
  "Adds native dependent Sigma and PSigma blocks with computed projections."
  [checked-environment]
  (let [sigma (kernel/add-inductive-block checked-environment sigma-spec)]
    (when-not (= :accepted (:status sigma))
      (throw (ex-info "Dependent Sigma proof-data block rejected"
                      {:result sigma})))
    (let [psigma (kernel/add-inductive-block (:environment sigma) psigma-spec)]
      (when-not (= :accepted (:status psigma))
        (throw (ex-info "Dependent PSigma proof-data block rejected"
                        {:result psigma})))
      (extend-specs (:environment psigma) dependent-sum-definition-specs))))

(defn extend-set-functions
  "Adds set conditionals, dependent restrictions, sequencing, and Pi.map."
  [checked-environment]
  (extend-specs checked-environment set-function-specs))

(defn extend-finite-sets
  "Adds constructive List-cover finiteness and its negation."
  [checked-environment]
  (extend-specs checked-environment finite-set-specs))

(defn extend-concepts [checked-environment]
  (extend-specs checked-environment concept-specs))

(defn extend-combinators [checked-environment]
  (extend-specs checked-environment combinator-specs))

(defn extend-collections
  "Adds corpus-selected collection operations without changing the historical
  prelude environment used by earlier reproducibility checkpoints."
  [checked-environment]
  (let [option-added (kernel/add-inductive-block checked-environment option-spec)]
    (when-not (= :accepted (:status option-added))
      (throw (ex-info "Option proof-data representation rejected"
                      {:result option-added})))
    (-> (:environment option-added)
        (as-> environment
            (reduce list-data/add-definition environment
                    list-data/definition-specs))
        (extend-specs
         (filterv #(not (contains? expanded-set-spec-names (:name %)))
                  collection-specs)))))

(defn extend-data [checked-environment]
  (reduce
   (fn [environment spec]
     (let [added (kernel/add-inductive-block environment spec)]
       (when-not (= :accepted (:status added))
         (throw (ex-info "Prelude data representation rejected"
                         {:alias (:block/alias spec) :result added})))
       (:environment added)))
   checked-environment
   (conj (vec inductive/initial-specs) list-data/list-spec)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-concepts extend-data))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.prelude))
