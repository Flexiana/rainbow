(ns rainbow.math.finite.set-indexed-union
  "Constructive finite unions over finite index sets."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def index-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort index-data-level])

(defn- set-of [level element]
  (function/app (function/const* 'set/Set [level]) element))

(defn- list-of [level element]
  (function/app (function/const* 'data/List [[:succ level]]) element))

(defn- nil-list [level element]
  (function/app (function/const* 'data/nil [[:succ level]]) element))

(defn- membership [level element source value]
  (function/app (function/const* 'list/membership [level])
                element source value))

(defn- equality [level element left right]
  (function/equality [:succ level] element left right))

(defn- finite [level element source]
  (function/app (function/const* 'set/finite [level]) element source))

(defn- subset [level element small large]
  (function/app (function/const* 'set/subset [level])
                element small large))

(defn- union [element left right]
  (function/app (function/const* 'set/union [U]) element left right))

(defn- list-indexed-union [element index family indices]
  (function/app (function/const* 'set/list-indexed-union [U V])
                element index family indices))

(defn- restricted-indexed-union [element index indices family]
  (function/app (function/const* 'set/restricted-indexed-union [U V])
                element index indices family))

(defn- indexed-union [element index family]
  (function/app (function/const* 'set/indexed-union [U index-data-level])
                element index family))

(defn- universal [level element]
  (function/app (function/const* 'set/universal [level]) element))

(def list-indexed-union-spec
  {:name 'set/list-indexed-union
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['A type-u] ['Index type-v]
     ['family (function/arrow 'Index (set-of U 'A))]]
    (function/arrow (list-of V 'Index) (set-of U 'A)))
   :value
   (function/lam
    [['A type-u] ['Index type-v]
     ['family (function/arrow 'Index (set-of U 'A))]
     ['indices (list-of V 'Index)]]
    (function/app
     (function/const* 'data/List.rec [index-data-level data-level])
     'Index
     (function/lam [['ignored (list-of V 'Index)]] (set-of U 'A))
     (function/lam [['ignored 'A]] (proposition/falsity))
     (function/lam
      [['head 'Index] ['tail (list-of V 'Index)]
       ['tail-union (set-of U 'A)]]
      (union 'A (function/app 'family 'head) 'tail-union))
     'indices))})

(def restricted-indexed-union-spec
  {:name 'set/restricted-indexed-union
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['A type-u] ['Index type-v]
     ['indices (set-of V 'Index)]
     ['family (function/arrow 'Index (set-of U 'A))]]
    (set-of U 'A))
   :value
   (function/lam
    [['A type-u] ['Index type-v]
     ['indices (set-of V 'Index)]
     ['family (function/arrow 'Index (set-of U 'A))]
     ['value 'A]]
    (proposition/existence
     index-data-level 'Index
     (function/lam
      [['index 'Index]]
      (proposition/conjunction
       (function/app 'indices 'index)
       (function/app 'family 'index 'value)))))})

(def restricted-indexed-union-member-spec
  (let [joined (restricted-indexed-union 'A 'Index 'indices 'family)]
    {:name 'set/restricted-indexed-union-member
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['index 'Index] ['index-member (function/app 'indices 'index)]
       ['value 'A]
       ['value-member (function/app 'family 'index 'value)]]
      (function/app joined 'value))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['index 'Index] ['index-member (function/app 'indices 'index)]
       ['value 'A]
       ['value-member (function/app 'family 'index 'value)]]
      (function/app
       (function/const* 'proposition/witness [index-data-level])
       'Index
       (function/lam
        [['candidate 'Index]]
        (proposition/conjunction
         (function/app 'indices 'candidate)
         (function/app 'family 'candidate 'value)))
       'index
       (function/app
        (function/const* 'proposition/conjoin [])
        (function/app 'indices 'index)
        (function/app 'family 'index 'value)
        'index-member 'value-member)))}))

(def list-indexed-union-member-spec
  (let [list-index (list-of V 'Index)
        motive
        (function/lam
         [['source list-index]]
         (function/forall
          [['index 'Index]
           ['index-member (membership V 'Index 'source 'index)]
           ['value 'A]
           ['value-member (function/app 'family 'index 'value)]]
          (function/app
           (list-indexed-union 'A 'Index 'family 'source)
           'value)))]
    {:name 'set/list-indexed-union-member
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['source list-index]
       ['index 'Index]
       ['index-member (membership V 'Index 'source 'index)]
       ['value 'A]
       ['value-member (function/app 'family 'index 'value)]]
      (function/app
       (list-indexed-union 'A 'Index 'family 'source)
       'value))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['source list-index]]
      (function/app
       (function/const* 'data/List.rec [index-data-level [:zero]])
       'Index motive
       (function/lam
        [['index 'Index]
         ['impossible
          (membership V 'Index (nil-list V 'Index) 'index)]
         ['value 'A]
         ['value-member (function/app 'family 'index 'value)]]
        (function/app
         (function/const* 'proposition/explode [])
         (function/app
          (list-indexed-union
           'A 'Index 'family (nil-list V 'Index))
          'value)
         'impossible))
       (function/lam
        [['head 'Index] ['tail list-index]
         ['induction-hypothesis (function/app motive 'tail)]
         ['index 'Index]
         ['index-member
          (membership V 'Index
                      (function/app
                       (function/const* 'data/cons [index-data-level])
                       'Index 'head 'tail)
                      'index)]
         ['value 'A]
         ['value-member (function/app 'family 'index 'value)]]
        (let [head-case (equality V 'Index 'index 'head)
              tail-case (membership V 'Index 'tail 'index)
              head-member (function/app 'family 'head 'value)
              tail-union
              (list-indexed-union 'A 'Index 'family 'tail)
              target
              (function/app
               (union 'A (function/app 'family 'head) tail-union)
               'value)]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-case tail-case target 'index-member
           (function/lam
            [['same head-case]]
            (function/app
             (function/const* 'proposition/left-disjunct [])
             head-member
             (function/app tail-union 'value)
             (function/app
              (function/const* 'equality/substitution [index-data-level])
              'Index 'index 'head 'same
              (function/lam
               [['candidate 'Index]]
               (function/app 'family 'candidate 'value))
              'value-member)))
           (function/lam
            [['tail-member tail-case]]
            (function/app
             (function/const* 'proposition/right-disjunct [])
             head-member
             (function/app tail-union 'value)
             (function/app
              'induction-hypothesis
              'index 'tail-member 'value 'value-member))))))
       'source))}))

(def finite-list-indexed-union-spec
  (let [list-index (list-of V 'Index)
        motive
        (function/lam
         [['source list-index]]
         (finite U 'A
                 (list-indexed-union 'A 'Index 'family 'source)))]
    {:name 'set/finite-list-indexed-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]
       ['source list-index]]
      (function/app motive 'source))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]
       ['source list-index]]
      (function/app
       (function/const* 'data/List.rec [index-data-level [:zero]])
       'Index motive
       (let [empty-set
             (list-indexed-union
              'A 'Index 'family (nil-list V 'Index))
             list-a (list-of U 'A)
             nil-a (nil-list U 'A)
             cover-predicate
             (function/lam
              [['enumeration list-a]]
              (function/forall
               [['value 'A]
                ['member (function/app empty-set 'value)]]
               (membership U 'A 'enumeration 'value)))]
         (function/app
          (function/const* 'proposition/witness [data-level])
          list-a cover-predicate nil-a
          (function/lam
           [['value 'A]
            ['impossible (function/app empty-set 'value)]]
           (function/app
            (function/const* 'proposition/explode [])
            (membership U 'A nil-a 'value)
            'impossible))))
       (function/lam
        [['head 'Index] ['tail list-index]
         ['tail-finite (function/app motive 'tail)]]
        (function/app
         (function/const* 'set/finite-union-preserved [U])
         'A
         (function/app 'family 'head)
         (list-indexed-union 'A 'Index 'family 'tail)
         (function/app 'family-finite 'head)
         'tail-finite))
       'source))}))

(def restricted-indexed-union-subset-list-spec
  (let [joined (restricted-indexed-union 'A 'Index 'indices 'family)
        list-joined
        (list-indexed-union 'A 'Index 'family 'enumeration)]
    {:name 'set/restricted-indexed-union-subset-list
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['enumeration (list-of V 'Index)]
       ['index-cover
        (function/forall
         [['index 'Index]
          ['member (function/app 'indices 'index)]]
         (membership V 'Index 'enumeration 'index))]]
      (subset U 'A joined list-joined))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['enumeration (list-of V 'Index)]
       ['index-cover
        (function/forall
         [['index 'Index]
          ['member (function/app 'indices 'index)]]
         (membership V 'Index 'enumeration 'index))]
       ['value 'A]
       ['member (function/app joined 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [index-data-level])
       'Index
       (function/lam
        [['index 'Index]]
        (proposition/conjunction
         (function/app 'indices 'index)
         (function/app 'family 'index 'value)))
       (function/app list-joined 'value)
       'member
       (function/lam
        [['index 'Index]
         ['both
          (proposition/conjunction
           (function/app 'indices 'index)
           (function/app 'family 'index 'value))]]
        (let [index-member
              (function/app
               (function/const* 'proposition/left [])
               (function/app 'indices 'index)
               (function/app 'family 'index 'value)
               'both)
              value-member
              (function/app
               (function/const* 'proposition/right [])
               (function/app 'indices 'index)
               (function/app 'family 'index 'value)
               'both)]
          (function/app
           (function/const* 'set/list-indexed-union-member [U V])
           'A 'Index 'family 'enumeration
           'index (function/app 'index-cover 'index index-member)
           'value value-member)))))}))

(def finite-restricted-indexed-union-spec
  (let [joined (restricted-indexed-union 'A 'Index 'indices 'family)
        target (finite U 'A joined)
        list-index (list-of V 'Index)
        cover-predicate
        (function/lam
         [['enumeration list-index]]
         (function/forall
          [['index 'Index]
           ['member (function/app 'indices 'index)]]
          (membership V 'Index 'enumeration 'index)))]
    {:name 'set/finite-restricted-indexed-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['indices-finite (finite V 'Index 'indices)]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]]
      target)
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['indices-finite (finite V 'Index 'indices)]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]]
      (function/app
       (function/const* 'proposition/use-witness [index-data-level])
       list-index cover-predicate target 'indices-finite
       (function/lam
        [['enumeration list-index]
         ['index-cover (function/app cover-predicate 'enumeration)]]
        (let [list-joined
              (list-indexed-union 'A 'Index 'family 'enumeration)]
          (function/app
           (function/const* 'set/finite-subset-preserved [U])
           'A joined list-joined
           (function/app
            (function/const*
             'set/restricted-indexed-union-subset-list [U V])
            'A 'Index 'indices 'family 'enumeration 'index-cover)
           (function/app
            (function/const* 'set/finite-list-indexed-union [U V])
            'A 'Index 'family 'family-finite 'enumeration))))))}))

(def restricted-indexed-union-subset-spec
  (let [restricted
        (restricted-indexed-union 'A 'Index 'indices 'family)
        unrestricted (indexed-union 'A 'Index 'family)]
    {:name 'set/restricted-indexed-union-subset
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]]
      (subset U 'A restricted unrestricted))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['indices (set-of V 'Index)]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['value 'A]
       ['member (function/app restricted 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [index-data-level])
       'Index
       (function/lam
        [['index 'Index]]
        (proposition/conjunction
         (function/app 'indices 'index)
         (function/app 'family 'index 'value)))
       (function/app unrestricted 'value)
       'member
       (function/lam
        [['index 'Index]
         ['both
          (proposition/conjunction
           (function/app 'indices 'index)
           (function/app 'family 'index 'value))]]
        (function/app
         (function/const* 'proposition/witness [index-data-level])
         'Index
         (function/lam
          [['candidate 'Index]]
          (function/app 'family 'candidate 'value))
         'index
         (function/app
          (function/const* 'proposition/right [])
          (function/app 'indices 'index)
          (function/app 'family 'index 'value)
          'both)))))}))

(def indexed-union-subset-universal-restricted-spec
  (let [all-indices (universal V 'Index)
        restricted
        (restricted-indexed-union 'A 'Index all-indices 'family)
        unrestricted (indexed-union 'A 'Index 'family)]
    {:name 'set/indexed-union-subset-universal-restricted
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]]
      (subset U 'A unrestricted restricted))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['value 'A]
       ['member (function/app unrestricted 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [index-data-level])
       'Index
       (function/lam
        [['index 'Index]]
        (function/app 'family 'index 'value))
       (function/app restricted 'value)
       'member
       (function/lam
        [['index 'Index]
         ['value-member (function/app 'family 'index 'value)]]
        (function/app
         (function/const* 'proposition/witness [index-data-level])
         'Index
         (function/lam
          [['candidate 'Index]]
          (proposition/conjunction
           (function/app all-indices 'candidate)
           (function/app 'family 'candidate 'value)))
         'index
         (function/app
          (function/const* 'proposition/conjoin [])
          (function/app all-indices 'index)
          (function/app 'family 'index 'value)
          (function/const* 'proposition/trivial [])
          'value-member)))))}))

(def finite-indexed-union-spec
  (let [all-indices (universal V 'Index)
        restricted
        (restricted-indexed-union 'A 'Index all-indices 'family)
        unrestricted (indexed-union 'A 'Index 'family)]
    {:name 'set/finite-indexed-union
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['index-type-finite (finite V 'Index all-indices)]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]]
      (finite U 'A unrestricted))
     :value
     (function/lam
      [['A type-u] ['Index type-v]
       ['family (function/arrow 'Index (set-of U 'A))]
       ['index-type-finite (finite V 'Index all-indices)]
       ['family-finite
        (function/forall
         [['index 'Index]]
         (finite U 'A (function/app 'family 'index)))]]
      (function/app
       (function/const* 'set/finite-subset-preserved [U])
       'A unrestricted restricted
       (function/app
        (function/const*
         'set/indexed-union-subset-universal-restricted [U V])
        'A 'Index 'family)
       (function/app
        (function/const* 'set/finite-restricted-indexed-union [U V])
        'A 'Index all-indices 'family
        'index-type-finite 'family-finite)))}))

(def definition-specs
  [list-indexed-union-spec restricted-indexed-union-spec])

(def theorem-specs
  [restricted-indexed-union-member-spec
   list-indexed-union-member-spec
   finite-list-indexed-union-spec
   restricted-indexed-union-subset-list-spec
   finite-restricted-indexed-union-spec
   restricted-indexed-union-subset-spec
   indexed-union-subset-universal-restricted-spec
   finite-indexed-union-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.set])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-set-indexed-union (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.set-indexed-union))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
