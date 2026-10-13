(ns rainbow.math.finite.set
  "Constructive finite-set theorems over native List-cover proof data."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def output-data-level [:succ W])
(def product-level [:max U V])
(def product-data-level [:succ product-level])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])
(def type-w [:sort output-data-level])

(defn set-of [element]
  (function/app (function/const* 'set/Set [U]) element))

(defn list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn target-set-of [element]
  (function/app (function/const* 'set/Set [V]) element))

(defn target-list-of [element]
  (function/app (function/const* 'data/List [target-data-level]) element))

(defn output-set-of [element]
  (function/app (function/const* 'set/Set [W]) element))

(defn output-list-of [element]
  (function/app (function/const* 'data/List [output-data-level]) element))

(defn finite [element source]
  (function/app (function/const* 'set/finite [U]) element source))

(defn infinite [element source]
  (function/app (function/const* 'set/infinite [U]) element source))

(defn nonempty [element source]
  (function/app (function/const* 'set/nonempty [U]) element source))

(defn target-nonempty [element source]
  (function/app (function/const* 'set/nonempty [V]) element source))

(defn insert [element selected source]
  (function/app (function/const* 'set/insert [U])
                element selected source))

(defn union [element left right]
  (function/app (function/const* 'set/union [U]) element left right))

(defn difference [element left right]
  (function/app (function/const* 'set/difference [U]) element left right))

(defn subset [element small large]
  (function/app (function/const* 'set/subset [U]) element small large))

(defn membership [element enumeration value]
  (function/app (function/const* 'list/membership [U])
                element enumeration value))

(defn target-membership [element enumeration value]
  (function/app (function/const* 'list/membership [V])
                element enumeration value))

(defn output-membership [element enumeration value]
  (function/app (function/const* 'list/membership [W])
                element enumeration value))

(defn equality [element left right]
  (function/app (function/const* 'equality/Eq [data-level])
                element left right))

(defn target-equality [element left right]
  (function/app (function/const* 'equality/Eq [target-data-level])
                element left right))

(defn output-equality [element left right]
  (function/app (function/const* 'equality/Eq [output-data-level])
                element left right))

(defn cover [element source enumeration]
  (function/forall
   [['value element]
    ['member (function/app source 'value)]]
   (membership element enumeration 'value)))

(defn cons-list [element selected enumeration]
  (function/app (function/const* 'data/cons [data-level])
                element selected enumeration))

(defn append-list [element left right]
  (function/app (function/const* 'list/append [data-level])
                element left right))

(defn map-list [source-element target-element mapping enumeration]
  (function/app (function/const* 'list/map
                                 [data-level target-data-level])
                source-element target-element mapping enumeration))

(defn map-target-list [source-element target-element mapping enumeration]
  (function/app (function/const* 'list/map
                                 [target-data-level output-data-level])
                source-element target-element mapping enumeration))

(defn append-output-list [element left right]
  (function/app (function/const* 'list/append [output-data-level])
                element left right))

(defn product-map-list
  [left-element right-element output-element mapping left-enumeration
   right-enumeration]
  (function/app (function/const* 'list/product-map [U V W])
                left-element right-element output-element mapping
                left-enumeration right-enumeration))

(defn image [source-element target-element mapping source]
  (function/app (function/const* 'set/image [U V])
                source-element target-element mapping source))

(defn preimage [source-element target-element mapping target]
  (function/app (function/const* 'set/preimage [U V])
                source-element target-element mapping target))

(defn target-finite [element source]
  (function/app (function/const* 'set/finite [V]) element source))

(defn target-infinite [element source]
  (function/app (function/const* 'set/infinite [V]) element source))

(defn maps-to [source-element target-element mapping source target]
  (function/app (function/const* 'set/maps-to [U V])
                source-element target-element mapping source target))

(defn injective-on [source-element target-element mapping source]
  (function/app (function/const* 'set/injective-on [U V])
                source-element target-element mapping source))

(defn surjective-on [source-element target-element mapping source target]
  (function/app (function/const* 'set/surjective-on [U V])
                source-element target-element mapping source target))

(defn target-cover [element source enumeration]
  (function/forall
   [['value element]
    ['member (function/app source 'value)]]
   (target-membership element enumeration 'value)))

(defn output-cover [element source enumeration]
  (function/forall
   [['value element]
    ['member (function/app source 'value)]]
   (output-membership element enumeration 'value)))

(defn image2 [left-element right-element output-element mapping left right]
  (function/app (function/const* 'set/image2 [U V W])
                left-element right-element output-element mapping left right))

(defn output-finite [element source]
  (function/app (function/const* 'set/finite [W]) element source))

(defn product-type [left-element right-element]
  (function/app
   (function/const* 'data/Product [data-level target-data-level])
   left-element right-element))

(defn pair-value [left-element right-element left right]
  (function/app
   (function/const* 'data/pair [data-level target-data-level])
   left-element right-element left right))

(defn first-value [left-element right-element pair]
  (function/app
   (function/const* 'product/first [data-level target-data-level])
   left-element right-element pair))

(defn second-value [left-element right-element pair]
  (function/app
   (function/const* 'product/second [data-level target-data-level])
   left-element right-element pair))

(defn product-set [left-element right-element left right]
  (function/app (function/const* 'set/product [U V])
                left-element right-element left right))

(defn product-list-of [left-element right-element]
  (function/app (function/const* 'data/List [product-data-level])
                (product-type left-element right-element)))

(defn product-membership [left-element right-element enumeration value]
  (function/app (function/const* 'list/membership [product-level])
                (product-type left-element right-element) enumeration value))

(defn product-cover [left-element right-element source enumeration]
  (function/forall
   [['value (product-type left-element right-element)]
    ['member (function/app source 'value)]]
   (product-membership left-element right-element enumeration 'value)))

(defn product-finite [left-element right-element source]
  (function/app (function/const* 'set/finite [product-level])
                (product-type left-element right-element) source))

(defn product-pair-list
  [left-element right-element left-enumeration right-enumeration]
  (let [product (product-type left-element right-element)
        pairing (function/lam
                 [['left left-element] ['right right-element]]
                 (pair-value left-element right-element 'left 'right))]
    (function/app (function/const* 'list/product-map [U V product-level])
                  left-element right-element product pairing
                  left-enumeration right-enumeration)))

(def membership-append-left-spec
  (let [list-a (list-of 'A)
        motive
        (function/lam
         [['left list-a]]
         (function/forall
          [['right list-a] ['value 'A]
           ['member (membership 'A 'left 'value)]]
          (membership 'A (append-list 'A 'left 'right) 'value)))
        nil-case
        (function/lam
         [['right list-a] ['value 'A]
          ['impossible (membership
                        'A
                        (function/app
                         (function/const* 'data/nil [data-level]) 'A)
                        'value)]]
         (function/app
          (function/const* 'proposition/explode [])
          (membership 'A 'right 'value) 'impossible))
        cons-case
        (function/lam
         [['head 'A] ['tail list-a]
          ['induction-hypothesis
           (function/forall
            [['right list-a] ['value 'A]
             ['member (membership 'A 'tail 'value)]]
            (membership 'A (append-list 'A 'tail 'right) 'value))]
          ['right list-a] ['value 'A]
          ['member
           (membership 'A (cons-list 'A 'head 'tail) 'value)]]
         (let [head-case (equality 'A 'value 'head)
               tail-case (membership 'A 'tail 'value)
               appended-tail-case
               (membership 'A (append-list 'A 'tail 'right) 'value)]
           (function/app
            (function/const* 'proposition/use-disjunction [])
            head-case tail-case
            (membership 'A
                        (cons-list 'A 'head
                                   (append-list 'A 'tail 'right))
                        'value)
            'member
            (function/lam
             [['at-head head-case]]
             (function/app
              (function/const* 'proposition/left-disjunct [])
              head-case appended-tail-case 'at-head))
            (function/lam
             [['in-tail tail-case]]
             (function/app
              (function/const* 'proposition/right-disjunct [])
              head-case appended-tail-case
              (function/app 'induction-hypothesis
                            'right 'value 'in-tail))))))]
    {:name 'list/membership-append-left
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['left list-a] ['right list-a] ['value 'A]
       ['member (membership 'A 'left 'value)]]
      (membership 'A (append-list 'A 'left 'right) 'value))
     :value
     (function/lam
      [['A type-u] ['left list-a]]
      (function/app
       (function/const* 'data/List.rec [data-level [:zero]])
       'A motive nil-case cons-case 'left))}))

(def membership-append-right-spec
  (let [list-a (list-of 'A)
        motive
        (function/lam
         [['left list-a]]
         (function/forall
          [['right list-a] ['value 'A]
           ['member (membership 'A 'right 'value)]]
          (membership 'A (append-list 'A 'left 'right) 'value)))
        nil-case
        (function/lam
         [['right list-a] ['value 'A]
          ['member (membership 'A 'right 'value)]]
         'member)
        cons-case
        (function/lam
         [['head 'A] ['tail list-a]
          ['induction-hypothesis
           (function/forall
            [['right list-a] ['value 'A]
             ['member (membership 'A 'right 'value)]]
            (membership 'A (append-list 'A 'tail 'right) 'value))]
          ['right list-a] ['value 'A]
          ['member (membership 'A 'right 'value)]]
         (let [head-case (equality 'A 'value 'head)
               appended-tail-case
               (membership 'A (append-list 'A 'tail 'right) 'value)]
           (function/app
            (function/const* 'proposition/right-disjunct [])
            head-case appended-tail-case
            (function/app 'induction-hypothesis 'right 'value 'member))))]
    {:name 'list/membership-append-right
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['left list-a] ['right list-a] ['value 'A]
       ['member (membership 'A 'right 'value)]]
      (membership 'A (append-list 'A 'left 'right) 'value))
     :value
     (function/lam
      [['A type-u] ['left list-a]]
      (function/app
       (function/const* 'data/List.rec [data-level [:zero]])
       'A motive nil-case cons-case 'left))}))

(def cover-cons-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        inserted (insert 'A 'selected 'source)
        enumeration (cons-list 'A 'selected 'enumeration)
        selected-case (equality 'A 'value 'selected)
        source-case (function/app 'source 'value)
        target (membership 'A enumeration 'value)]
    {:name 'list/cover-cons
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['selected 'A] ['source set-a]
       ['enumeration list-a]
       ['source-cover (cover 'A 'source 'enumeration)]]
      (cover 'A inserted enumeration))
     :value
     (function/lam
      [['A type-u] ['selected 'A] ['source set-a]
       ['enumeration list-a]
       ['source-cover (cover 'A 'source 'enumeration)]
       ['value 'A]
       ['inserted-member (proposition/disjunction selected-case source-case)]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       selected-case source-case target 'inserted-member
       (function/lam
        [['selected-equality selected-case]]
        (function/app
         (function/const* 'proposition/left-disjunct [])
         selected-case (membership 'A 'enumeration 'value)
         'selected-equality))
       (function/lam
        [['source-member source-case]]
        (function/app
         (function/const* 'proposition/right-disjunct [])
         selected-case (membership 'A 'enumeration 'value)
         (function/app 'source-cover 'value 'source-member)))))}))

(def finite-insert-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        inserted (insert 'A 'selected 'source)
        source-cover (function/lam
                      [['enumeration list-a]]
                      (cover 'A 'source 'enumeration))
        inserted-cover (function/lam
                        [['enumeration list-a]]
                        (cover 'A inserted 'enumeration))
        target (finite 'A inserted)]
    {:name 'set/finite-insert-preserved
     :universes ['u]
     ;; Binder modes mirror the pinned theorem shape so exact reuse can remain
     ;; transparent rather than relying on a name-level foreign adapter.
     :type
     (function/forall
      [['A type-u :implicit]
       ['selected 'A :explicit]
       ['source set-a :implicit]
       ['source-finite (finite 'A 'source) :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['selected 'A :explicit]
       ['source set-a :implicit]
       ['source-finite (finite 'A 'source) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a source-cover target 'source-finite
       (function/lam
        [['enumeration list-a]
         ['source-cover-evidence (cover 'A 'source 'enumeration)]]
        (function/app
         (function/const* 'proposition/witness [data-level])
         list-a inserted-cover
         (cons-list 'A 'selected 'enumeration)
         (function/app
          (function/const* 'list/cover-cons [U])
          'A 'selected 'source 'enumeration 'source-cover-evidence)))))}))

(def cover-append-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        joined (union 'A 'left-source 'right-source)
        enumeration (append-list 'A 'left-enumeration 'right-enumeration)
        left-case (function/app 'left-source 'value)
        right-case (function/app 'right-source 'value)
        target (membership 'A enumeration 'value)]
    {:name 'list/cover-append
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left-source set-a] ['right-source set-a]
       ['left-enumeration list-a] ['right-enumeration list-a]
       ['left-cover (cover 'A 'left-source 'left-enumeration)]
       ['right-cover (cover 'A 'right-source 'right-enumeration)]]
      (cover 'A joined enumeration))
     :value
     (function/lam
      [['A type-u]
       ['left-source set-a] ['right-source set-a]
       ['left-enumeration list-a] ['right-enumeration list-a]
       ['left-cover (cover 'A 'left-source 'left-enumeration)]
       ['right-cover (cover 'A 'right-source 'right-enumeration)]
       ['value 'A]
       ['joined-member (proposition/disjunction left-case right-case)]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       left-case right-case target 'joined-member
       (function/lam
        [['left-member left-case]]
        (function/app
         (function/const* 'list/membership-append-left [U])
         'A 'left-enumeration 'right-enumeration 'value
         (function/app 'left-cover 'value 'left-member)))
       (function/lam
        [['right-member right-case]]
        (function/app
         (function/const* 'list/membership-append-right [U])
         'A 'left-enumeration 'right-enumeration 'value
         (function/app 'right-cover 'value 'right-member)))))}))

(def finite-union-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        joined (union 'A 'left 'right)
        left-cover (function/lam
                    [['enumeration list-a]]
                    (cover 'A 'left 'enumeration))
        right-cover (function/lam
                     [['enumeration list-a]]
                     (cover 'A 'right 'enumeration))
        joined-cover (function/lam
                      [['enumeration list-a]]
                      (cover 'A joined 'enumeration))
        target (finite 'A joined)]
    {:name 'set/finite-union-preserved
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left set-a :implicit]
       ['right set-a :implicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (finite 'A 'right) :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['left set-a :implicit]
       ['right set-a :implicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (finite 'A 'right) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a left-cover target 'left-finite
       (function/lam
        [['left-enumeration list-a]
         ['left-cover-evidence (cover 'A 'left 'left-enumeration)]]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         list-a right-cover target 'right-finite
         (function/lam
          [['right-enumeration list-a]
           ['right-cover-evidence (cover 'A 'right 'right-enumeration)]]
          (function/app
           (function/const* 'proposition/witness [data-level])
           list-a joined-cover
           (append-list 'A 'left-enumeration 'right-enumeration)
           (function/app
            (function/const* 'list/cover-append [U])
            'A 'left 'right 'left-enumeration 'right-enumeration
            'left-cover-evidence 'right-cover-evidence)))))))}))

(def finite-subset-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        large-cover (function/lam
                     [['enumeration list-a]]
                     (cover 'A 'large 'enumeration))
        small-cover (function/lam
                     [['enumeration list-a]]
                     (cover 'A 'small 'enumeration))
        target (finite 'A 'small)]
    {:name 'set/finite-subset-preserved
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['small set-a] ['large set-a]
       ['inclusion (subset 'A 'small 'large)]
       ['large-finite (finite 'A 'large)]]
      target)
     :value
     (function/lam
      [['A type-u] ['small set-a] ['large set-a]
       ['inclusion (subset 'A 'small 'large)]
       ['large-finite (finite 'A 'large)]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a large-cover target 'large-finite
       (function/lam
        [['enumeration list-a]
         ['large-cover-evidence (cover 'A 'large 'enumeration)]]
        (function/app
         (function/const* 'proposition/witness [data-level])
         list-a small-cover 'enumeration
         (function/lam
          [['value 'A] ['small-member (function/app 'small 'value)]]
          (function/app
           'large-cover-evidence 'value
           (function/app 'inclusion 'value 'small-member)))))))}))

(def finite-insert-equivalence-spec
  (let [set-a (set-of 'A)
        inserted (insert 'A 'selected 'source)
        inserted-finite (finite 'A inserted)
        source-finite (finite 'A 'source)
        selected-case (equality 'A 'value 'selected)
        source-case (function/app 'source 'value)
        inclusion
        (function/lam
         [['value 'A] ['source-member source-case]]
         (function/app
          (function/const* 'proposition/right-disjunct [])
          selected-case source-case 'source-member))]
    {:name 'set/finite-insert-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['selected 'A :implicit]]
      (proposition/equivalence inserted-finite source-finite))
     :value
     (function/lam
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['selected 'A :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       inserted-finite source-finite
       (function/lam
        [['inserted-finite-evidence inserted-finite]]
        (function/app
         (function/const* 'set/finite-subset-preserved [U])
         'A 'source inserted inclusion 'inserted-finite-evidence))
       (function/lam
        [['source-finite-evidence source-finite]]
        (function/app
         (function/const* 'set/finite-insert-preserved [U])
         'A 'selected 'source 'source-finite-evidence))))}))

(def finite-union-equivalence-spec
  (let [set-a (set-of 'A)
        joined (union 'A 'left 'right)
        joined-finite (finite 'A joined)
        left-finite (finite 'A 'left)
        right-finite (finite 'A 'right)
        both-finite (proposition/conjunction left-finite right-finite)
        left-case (function/app 'left 'value)
        right-case (function/app 'right 'value)
        left-inclusion
        (function/lam
         [['value 'A] ['left-member left-case]]
         (function/app
          (function/const* 'proposition/left-disjunct [])
          left-case right-case 'left-member))
        right-inclusion
        (function/lam
         [['value 'A] ['right-member right-case]]
         (function/app
          (function/const* 'proposition/right-disjunct [])
          left-case right-case 'right-member))]
    {:name 'set/finite-union-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left set-a :implicit]
       ['right set-a :implicit]]
      (proposition/equivalence joined-finite both-finite))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left set-a :implicit]
       ['right set-a :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       joined-finite both-finite
       (function/lam
        [['joined-finite-evidence joined-finite]]
        (function/app
         (function/const* 'proposition/conjoin [])
         left-finite right-finite
         (function/app
          (function/const* 'set/finite-subset-preserved [U])
          'A 'left joined left-inclusion 'joined-finite-evidence)
         (function/app
          (function/const* 'set/finite-subset-preserved [U])
          'A 'right joined right-inclusion 'joined-finite-evidence)))
       (function/lam
        [['both-finite-evidence both-finite]]
        (function/app
         (function/const* 'set/finite-union-preserved [U])
         'A 'left 'right
         (function/app
          (function/const* 'proposition/left [])
          left-finite right-finite 'both-finite-evidence)
          (function/app
           (function/const* 'proposition/right [])
           left-finite right-finite 'both-finite-evidence)))))}))

(def product-map-list-spec
  (let [list-a (list-of 'A)
        list-b (target-list-of 'B)
        list-c (output-list-of 'C)]
    {:name 'list/product-map
     :kind :definition
     :universes ['u 'v 'w]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left-enumeration list-a] ['right-enumeration list-b]]
      list-c)
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left-enumeration list-a] ['right-enumeration list-b]]
      (function/app
       (function/const* 'data/List.rec [data-level output-data-level])
       'A
       (function/lam [['ignored list-a]] list-c)
       (function/app (function/const* 'data/nil [output-data-level]) 'C)
       (function/lam
        [['head 'A] ['tail list-a] ['tail-product list-c]]
        (append-output-list
         'C
         (map-target-list 'B 'C (function/app 'mapping 'head)
                          'right-enumeration)
         'tail-product))
       'left-enumeration))}))

(def membership-map-spec
  (let [list-a (list-of 'A)
        list-b (target-list-of 'B)
        motive
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A]
           ['member (membership 'A 'enumeration 'value)]]
          (target-membership
           'B (map-list 'A 'B 'mapping 'enumeration)
           (function/app 'mapping 'value))))
        nil-case
        (function/lam
         [['value 'A]
          ['impossible
           (membership
            'A (function/app (function/const* 'data/nil [data-level]) 'A)
            'value)]]
         (function/app
          (function/const* 'proposition/explode [])
          (target-membership
           'B (function/app (function/const* 'data/nil [target-data-level])
                            'B)
           (function/app 'mapping 'value))
          'impossible))
        cons-case
        (function/lam
         [['head 'A] ['tail list-a]
          ['induction-hypothesis
           (function/forall
            [['value 'A]
             ['member (membership 'A 'tail 'value)]]
            (target-membership
             'B (map-list 'A 'B 'mapping 'tail)
             (function/app 'mapping 'value)))]
          ['value 'A]
          ['member (membership 'A (cons-list 'A 'head 'tail) 'value)]]
         (let [source-head (equality 'A 'value 'head)
               source-tail (membership 'A 'tail 'value)
               target-head
               (target-equality 'B (function/app 'mapping 'value)
                                (function/app 'mapping 'head))
               target-tail
               (target-membership
                'B (map-list 'A 'B 'mapping 'tail)
                (function/app 'mapping 'value))]
           (function/app
            (function/const* 'proposition/use-disjunction [])
            source-head source-tail
            (target-membership
             'B
             (function/app
              (function/const* 'data/cons [target-data-level])
              'B (function/app 'mapping 'head)
              (map-list 'A 'B 'mapping 'tail))
             (function/app 'mapping 'value))
            'member
            (function/lam
             [['at-head source-head]]
             (function/app
              (function/const* 'proposition/left-disjunct [])
              target-head target-tail
              (function/app
               (function/const* 'equality/congruent-function
                                [data-level target-data-level])
               'A 'B 'mapping 'value 'head 'at-head)))
            (function/lam
             [['in-tail source-tail]]
             (function/app
              (function/const* 'proposition/right-disjunct [])
              target-head target-tail
              (function/app 'induction-hypothesis 'value 'in-tail))))))]
    {:name 'list/membership-map
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)]
       ['enumeration list-a] ['value 'A]
       ['member (membership 'A 'enumeration 'value)]]
      (target-membership
       'B (map-list 'A 'B 'mapping 'enumeration)
       (function/app 'mapping 'value)))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)] ['enumeration list-a]]
      (function/app
       (function/const* 'data/List.rec [data-level [:zero]])
       'A motive nil-case cons-case 'enumeration))}))

(def membership-product-map-spec
  (let [list-a (list-of 'A)
        list-b (target-list-of 'B)
        list-c (output-list-of 'C)
        motive
        (function/lam
         [['left-enumeration list-a]]
         (function/forall
          [['left-value 'A]
           ['left-member (membership 'A 'left-enumeration 'left-value)]
           ['right-value 'B]
           ['right-member
            (target-membership 'B 'right-enumeration 'right-value)]]
          (output-membership
           'C
           (product-map-list 'A 'B 'C 'mapping
                             'left-enumeration 'right-enumeration)
           (function/app 'mapping 'left-value 'right-value))))
        nil-case
        (function/lam
         [['left-value 'A]
          ['impossible
           (membership
            'A (function/app (function/const* 'data/nil [data-level]) 'A)
            'left-value)]
          ['right-value 'B]
          ['right-member
           (target-membership 'B 'right-enumeration 'right-value)]]
         (function/app
          (function/const* 'proposition/explode [])
          (output-membership
           'C (function/app (function/const* 'data/nil [output-data-level])
                            'C)
           (function/app 'mapping 'left-value 'right-value))
          'impossible))
        cons-case
        (function/lam
         [['head 'A] ['tail list-a]
          ['induction-hypothesis
           (function/forall
            [['left-value 'A]
             ['left-member (membership 'A 'tail 'left-value)]
             ['right-value 'B]
             ['right-member
              (target-membership 'B 'right-enumeration 'right-value)]]
            (output-membership
             'C
             (product-map-list 'A 'B 'C 'mapping
                               'tail 'right-enumeration)
             (function/app 'mapping 'left-value 'right-value)))]
          ['left-value 'A]
          ['left-member
           (membership 'A (cons-list 'A 'head 'tail) 'left-value)]
          ['right-value 'B]
          ['right-member
           (target-membership 'B 'right-enumeration 'right-value)]]
         (let [source-head (equality 'A 'left-value 'head)
               source-tail (membership 'A 'tail 'left-value)
               head-image
               (map-target-list 'B 'C (function/app 'mapping 'head)
                                'right-enumeration)
               tail-product
               (product-map-list 'A 'B 'C 'mapping
                                 'tail 'right-enumeration)
               product-enumeration
               (append-output-list 'C head-image tail-product)
               wanted (function/app 'mapping 'left-value 'right-value)]
           (function/app
            (function/const* 'proposition/use-disjunction [])
            source-head source-tail
            (output-membership 'C product-enumeration wanted)
            'left-member
            (function/lam
             [['at-head source-head]]
             (let [head-value (function/app 'mapping 'head 'right-value)
                   mapped-right
                   (function/app
                    (function/const* 'list/membership-map [V W])
                    'B 'C (function/app 'mapping 'head)
                    'right-enumeration 'right-value 'right-member)
                   appended-head
                   (function/app
                    (function/const* 'list/membership-append-left [W])
                    'C head-image tail-product head-value mapped-right)
                   mapped-equality
                   (function/app
                    (function/const* 'equality/congruent-function
                                     [data-level output-data-level])
                    'A 'C
                    (function/lam
                     [['candidate 'A]]
                     (function/app 'mapping 'candidate 'right-value))
                    'left-value 'head 'at-head)]
               (function/app
                (function/const* 'equality/reverse-substitution
                                 [output-data-level])
                'C wanted head-value mapped-equality
                (function/lam
                 [['candidate 'C]]
                 (output-membership 'C product-enumeration 'candidate))
                appended-head)))
            (function/lam
             [['in-tail source-tail]]
             (function/app
              (function/const* 'list/membership-append-right [W])
              'C head-image tail-product wanted
              (function/app 'induction-hypothesis
                            'left-value 'in-tail
                            'right-value 'right-member))))))]
    {:name 'list/membership-product-map
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left-enumeration list-a] ['right-enumeration list-b]
       ['left-value 'A]
       ['left-member (membership 'A 'left-enumeration 'left-value)]
       ['right-value 'B]
       ['right-member
        (target-membership 'B 'right-enumeration 'right-value)]]
      (output-membership
       'C
       (product-map-list 'A 'B 'C 'mapping
                         'left-enumeration 'right-enumeration)
       (function/app 'mapping 'left-value 'right-value)))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left-enumeration list-a] ['right-enumeration list-b]]
      (function/app
       (function/const* 'data/List.rec [data-level [:zero]])
       'A motive nil-case cons-case 'left-enumeration))}))

(def product-eta-spec
  (let [product (product-type 'A 'B)
        motive
        (function/lam
         [['value product]]
         (function/app
          (function/const* 'equality/Eq [product-data-level])
          product
          (pair-value 'A 'B
                      (first-value 'A 'B 'value)
                      (second-value 'A 'B 'value))
          'value))]
    {:name 'product/eta
     :universes ['u 'v]
     :type (function/forall [['A type-u] ['B type-v] ['value product]]
                           (function/app motive 'value))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['value product]]
      (function/app
       (function/const* 'data/Product.rec
                        [data-level target-data-level [:zero]])
       'A 'B motive
       (function/lam
        [['left 'A] ['right 'B]]
        (function/app
         (function/const* 'equality/reflexive [product-data-level])
         product (pair-value 'A 'B 'left 'right)))
       'value))}))

(def cover-image-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        mapped-enumeration (map-list 'A 'B 'mapping 'enumeration)
        mapped-source (image 'A 'B 'mapping 'source)
        target (target-membership 'B mapped-enumeration 'value)
        image-predicate
        (function/lam
         [['input 'A]]
         (proposition/conjunction
          (function/app 'source 'input)
          (target-equality 'B (function/app 'mapping 'input) 'value)))]
    {:name 'list/cover-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)] ['source set-a]
       ['enumeration list-a]
       ['source-cover (cover 'A 'source 'enumeration)]]
      (target-cover 'B mapped-source mapped-enumeration))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['mapping (function/arrow 'A 'B)] ['source set-a]
       ['enumeration list-a]
       ['source-cover (cover 'A 'source 'enumeration)]
       ['value 'B]
       ['image-member (function/app mapped-source 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A image-predicate target 'image-member
       (function/lam
        [['input 'A]
         ['both
          (proposition/conjunction
           (function/app 'source 'input)
           (target-equality 'B (function/app 'mapping 'input) 'value))]]
        (let [source-member
              (function/app
               (function/const* 'proposition/left [])
               (function/app 'source 'input)
               (target-equality 'B (function/app 'mapping 'input) 'value)
               'both)
              image-equality
              (function/app
               (function/const* 'proposition/right [])
               (function/app 'source 'input)
               (target-equality 'B (function/app 'mapping 'input) 'value)
               'both)
              mapped-member
              (function/app
               (function/const* 'list/membership-map [U V])
               'A 'B 'mapping 'enumeration 'input
               (function/app 'source-cover 'input source-member))]
          (function/app
           (function/const* 'equality/substitution [target-data-level])
           'B (function/app 'mapping 'input) 'value image-equality
           (function/lam
            [['candidate 'B]]
            (target-membership 'B mapped-enumeration 'candidate))
           mapped-member)))))}))

(def finite-image-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        list-b (target-list-of 'B)
        mapped-source (image 'A 'B 'mapping 'source)
        source-cover
        (function/lam
         [['enumeration list-a]]
         (cover 'A 'source 'enumeration))
        mapped-cover
        (function/lam
         [['mapped-enumeration list-b]]
         (target-cover 'B mapped-source 'mapped-enumeration))
        target (target-finite 'B mapped-source)]
    {:name 'set/finite-image-preserved
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['source-finite (finite 'A 'source) :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['source set-a :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['source-finite (finite 'A 'source) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a source-cover target 'source-finite
       (function/lam
        [['enumeration list-a]
         ['source-cover-evidence (cover 'A 'source 'enumeration)]]
        (function/app
         (function/const* 'proposition/witness [target-data-level])
         list-b mapped-cover
         (map-list 'A 'B 'mapping 'enumeration)
         (function/app
          (function/const* 'list/cover-image [U V])
          'A 'B 'mapping 'source 'enumeration
          'source-cover-evidence)))))}))

(def cover-image2-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        list-a (list-of 'A)
        list-b (target-list-of 'B)
        enumeration
        (product-map-list 'A 'B 'C 'mapping
                          'left-enumeration 'right-enumeration)
        mapped-source (image2 'A 'B 'C 'mapping 'left 'right)
        target (output-membership 'C enumeration 'value)
        inner-predicate
        (function/lam
         [['right-input 'B]]
         (proposition/conjunction
          (function/app 'right 'right-input)
          (output-equality
           'C (function/app 'mapping 'left-input 'right-input) 'value)))
        outer-predicate
        (function/lam
         [['left-input 'A]]
         (proposition/conjunction
          (function/app 'left 'left-input)
          (proposition/existence target-data-level 'B inner-predicate)))]
    {:name 'list/cover-image2
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left set-a] ['right set-b]
       ['left-enumeration list-a] ['right-enumeration list-b]
       ['left-cover (cover 'A 'left 'left-enumeration)]
       ['right-cover (target-cover 'B 'right 'right-enumeration)]]
      (output-cover 'C mapped-source enumeration))
     :value
     (function/lam
      [['A type-u] ['B type-v] ['C type-w]
       ['mapping (function/arrow 'A 'B 'C)]
       ['left set-a] ['right set-b]
       ['left-enumeration list-a] ['right-enumeration list-b]
       ['left-cover (cover 'A 'left 'left-enumeration)]
       ['right-cover (target-cover 'B 'right 'right-enumeration)]
       ['value 'C]
       ['image-member (function/app mapped-source 'value)]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A outer-predicate target 'image-member
       (function/lam
        [['left-input 'A]
         ['left-both
          (proposition/conjunction
           (function/app 'left 'left-input)
           (proposition/existence target-data-level 'B inner-predicate))]]
        (let [left-member
              (function/app
               (function/const* 'proposition/left [])
               (function/app 'left 'left-input)
               (proposition/existence target-data-level 'B inner-predicate)
               'left-both)
              right-exists
              (function/app
               (function/const* 'proposition/right [])
               (function/app 'left 'left-input)
               (proposition/existence target-data-level 'B inner-predicate)
               'left-both)]
          (function/app
           (function/const* 'proposition/use-witness [target-data-level])
           'B inner-predicate target right-exists
           (function/lam
            [['right-input 'B]
             ['right-both
              (proposition/conjunction
               (function/app 'right 'right-input)
               (output-equality
                'C (function/app 'mapping 'left-input 'right-input)
                'value))]]
            (let [right-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app 'right 'right-input)
                   (output-equality
                    'C (function/app 'mapping 'left-input 'right-input)
                    'value)
                   'right-both)
                  image-equality
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app 'right 'right-input)
                   (output-equality
                    'C (function/app 'mapping 'left-input 'right-input)
                    'value)
                   'right-both)
                  product-member
                  (function/app
                   (function/const* 'list/membership-product-map [U V W])
                   'A 'B 'C 'mapping
                   'left-enumeration 'right-enumeration
                   'left-input
                   (function/app 'left-cover 'left-input left-member)
                   'right-input
                   (function/app 'right-cover 'right-input right-member))]
              (function/app
               (function/const* 'equality/substitution [output-data-level])
               'C (function/app 'mapping 'left-input 'right-input)
               'value image-equality
               (function/lam
                [['candidate 'C]]
                (output-membership 'C enumeration 'candidate))
               product-member))))))))}))

(def finite-image2-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        list-a (list-of 'A)
        list-b (target-list-of 'B)
        list-c (output-list-of 'C)
        mapped-source (image2 'A 'B 'C 'mapping 'left 'right)
        left-cover
        (function/lam
         [['left-enumeration list-a]]
         (cover 'A 'left 'left-enumeration))
        right-cover
        (function/lam
         [['right-enumeration list-b]]
         (target-cover 'B 'right 'right-enumeration))
        mapped-cover
        (function/lam
         [['enumeration list-c]]
         (output-cover 'C mapped-source 'enumeration))
        target (output-finite 'C mapped-source)]
    {:name 'set/finite-image2-preserved
     :universes ['u 'v 'w]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['C type-w :implicit]
       ['left set-a :implicit]
       ['right set-b :implicit]
       ['mapping (function/arrow 'A 'B 'C) :explicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (target-finite 'B 'right) :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['C type-w :implicit]
       ['left set-a :implicit]
       ['right set-b :implicit]
       ['mapping (function/arrow 'A 'B 'C) :explicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (target-finite 'B 'right) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a left-cover target 'left-finite
       (function/lam
        [['left-enumeration list-a]
         ['left-cover-evidence (cover 'A 'left 'left-enumeration)]]
        (function/app
         (function/const* 'proposition/use-witness [target-data-level])
         list-b right-cover target 'right-finite
         (function/lam
          [['right-enumeration list-b]
           ['right-cover-evidence
            (target-cover 'B 'right 'right-enumeration)]]
          (function/app
           (function/const* 'proposition/witness [output-data-level])
           list-c mapped-cover
           (product-map-list 'A 'B 'C 'mapping
                             'left-enumeration 'right-enumeration)
           (function/app
            (function/const* 'list/cover-image2 [U V W])
            'A 'B 'C 'mapping 'left 'right
            'left-enumeration 'right-enumeration
            'left-cover-evidence 'right-cover-evidence)))))))}))

(def cover-product-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        list-a (list-of 'A)
        list-b (target-list-of 'B)
        product (product-type 'A 'B)
        source (product-set 'A 'B 'left 'right)
        enumeration
        (product-pair-list 'A 'B 'left-enumeration 'right-enumeration)
        left-value (first-value 'A 'B 'value)
        right-value (second-value 'A 'B 'value)
        left-member (function/app 'left left-value)
        right-member (function/app 'right right-value)
        target (product-membership 'A 'B enumeration 'value)
        pairing
        (function/lam
         [['left-value 'A] ['right-value 'B]]
         (pair-value 'A 'B 'left-value 'right-value))]
    {:name 'list/cover-product
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u] ['B type-v]
       ['left set-a] ['right set-b]
       ['left-enumeration list-a] ['right-enumeration list-b]
       ['left-cover (cover 'A 'left 'left-enumeration)]
       ['right-cover (target-cover 'B 'right 'right-enumeration)]]
      (product-cover 'A 'B source enumeration))
     :value
     (function/lam
      [['A type-u] ['B type-v]
       ['left set-a] ['right set-b]
       ['left-enumeration list-a] ['right-enumeration list-b]
       ['left-cover (cover 'A 'left 'left-enumeration)]
       ['right-cover (target-cover 'B 'right 'right-enumeration)]
       ['value product]
       ['member (proposition/conjunction left-member right-member)]]
      (let [left-evidence
            (function/app
             (function/const* 'proposition/left [])
             left-member right-member 'member)
            right-evidence
            (function/app
             (function/const* 'proposition/right [])
             left-member right-member 'member)
            pair (pair-value 'A 'B left-value right-value)
            pair-member
            (function/app
             (function/const* 'list/membership-product-map
                              [U V product-level])
             'A 'B product pairing
             'left-enumeration 'right-enumeration
             left-value
             (function/app 'left-cover left-value left-evidence)
             right-value
             (function/app 'right-cover right-value right-evidence))
            eta
            (function/app
             (function/const* 'product/eta [U V])
             'A 'B 'value)]
        (function/app
         (function/const* 'equality/substitution [product-data-level])
         product pair 'value eta
         (function/lam
          [['candidate product]]
          (product-membership 'A 'B enumeration 'candidate))
         pair-member)))}))

(def finite-product-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        list-a (list-of 'A)
        list-b (target-list-of 'B)
        product-list (product-list-of 'A 'B)
        source (product-set 'A 'B 'left 'right)
        left-cover
        (function/lam
         [['left-enumeration list-a]]
         (cover 'A 'left 'left-enumeration))
        right-cover
        (function/lam
         [['right-enumeration list-b]]
         (target-cover 'B 'right 'right-enumeration))
        source-cover
        (function/lam
         [['enumeration product-list]]
         (product-cover 'A 'B source 'enumeration))
        target (product-finite 'A 'B source)]
    {:name 'set/finite-product-preserved
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['left set-a :implicit]
       ['right set-b :implicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (target-finite 'B 'right) :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['left set-a :implicit]
       ['right set-b :implicit]
       ['left-finite (finite 'A 'left) :explicit]
       ['right-finite (target-finite 'B 'right) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a left-cover target 'left-finite
       (function/lam
        [['left-enumeration list-a]
         ['left-cover-evidence (cover 'A 'left 'left-enumeration)]]
        (function/app
         (function/const* 'proposition/use-witness [target-data-level])
         list-b right-cover target 'right-finite
         (function/lam
          [['right-enumeration list-b]
           ['right-cover-evidence
            (target-cover 'B 'right 'right-enumeration)]]
          (function/app
           (function/const* 'proposition/witness [product-data-level])
           product-list source-cover
           (product-pair-list 'A 'B
                              'left-enumeration 'right-enumeration)
           (function/app
            (function/const* 'list/cover-product [U V])
            'A 'B 'left 'right
            'left-enumeration 'right-enumeration
            'left-cover-evidence 'right-cover-evidence)))))))}))

(def finite-of-surjection-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        mapped-source (image 'A 'B 'mapping 'source)
        target-finite-value (target-finite 'B 'target)
        image-finite (target-finite 'B mapped-source)
        inclusion
        (function/lam
         [['value 'B]
          ['target-member (function/app 'target 'value)]]
         (function/app 'surjection 'value 'target-member))]
    {:name 'set/finite-of-surjection
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['source set-a :implicit]
       ['target set-b :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['surjection
        (surjective-on 'A 'B 'mapping 'source 'target) :explicit]
       ['source-finite (finite 'A 'source) :explicit]]
      target-finite-value)
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['source set-a :implicit]
       ['target set-b :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['surjection
        (surjective-on 'A 'B 'mapping 'source 'target) :explicit]
       ['source-finite (finite 'A 'source) :explicit]]
      (function/app
       (function/const* 'set/finite-subset-preserved [V])
       'B 'target mapped-source inclusion
       (function/app
        (function/const* 'set/finite-image-preserved [U V])
        'A 'B 'source 'mapping 'source-finite)))}))

(def infinite-mono-spec
  (let [set-a (set-of 'A)]
    {:name 'set/infinite-mono
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['small set-a :implicit]
       ['large set-a :implicit]
       ['inclusion (subset 'A 'small 'large) :explicit]
       ['small-infinite (infinite 'A 'small) :explicit]]
      (infinite 'A 'large))
     :value
     (function/lam
      [['A type-u :implicit]
       ['small set-a :implicit]
       ['large set-a :implicit]
       ['inclusion (subset 'A 'small 'large) :explicit]
       ['small-infinite (infinite 'A 'small) :explicit]
       ['large-finite (finite 'A 'large)]]
      (function/app
       'small-infinite
       (function/app
        (function/const* 'set/finite-subset-preserved [U])
        'A 'small 'large 'inclusion 'large-finite)))}))

(def infinite-of-image-spec
  (let [set-a (set-of 'A)
        mapped-source (image 'A 'B 'mapping 'source)]
    {:name 'set/infinite-of-image
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['source set-a :implicit]
       ['image-infinite (target-infinite 'B mapped-source) :explicit]]
      (infinite 'A 'source))
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['source set-a :implicit]
       ['image-infinite (target-infinite 'B mapped-source) :explicit]
       ['source-finite (finite 'A 'source)]]
      (function/app
       'image-infinite
       (function/app
        (function/const* 'set/finite-image-preserved [U V])
        'A 'B 'source 'mapping 'source-finite)))}))

(def finite-seq-spec
  (let [mapping-type (function/arrow 'A 'B)
        mappings
        (function/app (function/const* 'set/Set [[:max U V]]) mapping-type)
        inputs (set-of 'A)
        sequenced
        (function/app (function/const* 'set/seq [U V])
                      'A 'B 'mapping-set 'input-set)
        apply-mapping
        (function/lam
         [['mapping mapping-type] ['value 'A]]
         (function/app 'mapping 'value))]
    {:name 'set/finite-seq-preserved
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['mapping-set mappings :implicit]
       ['input-set inputs :implicit]
       ['mappings-finite
        (function/app (function/const* 'set/finite [[:max U V]])
                      mapping-type 'mapping-set) :explicit]
       ['inputs-finite (finite 'A 'input-set) :explicit]]
      (target-finite 'B sequenced))
     :value
     (function/lam
      [['A type-u :implicit]
       ['B type-v :implicit]
       ['mapping-set mappings :implicit]
       ['input-set inputs :implicit]
       ['mappings-finite
        (function/app (function/const* 'set/finite [[:max U V]])
                      mapping-type 'mapping-set) :explicit]
       ['inputs-finite (finite 'A 'input-set) :explicit]]
      (function/app
       (function/const* 'set/finite-image2-preserved
                        [[:max U V] U V])
       mapping-type 'A 'B 'mapping-set 'input-set
       apply-mapping 'mappings-finite 'inputs-finite))}))

(def finite-of-preimage-under-surjection-spec
  (let [set-b (target-set-of 'B)
        source (preimage 'A 'B 'mapping 'target)
        global-surjection
        (function/surjective data-level target-data-level
                              'A 'B 'mapping)
        restricted-surjection
        (function/lam
         [['value 'B :implicit]
          ['target-member (function/app 'target 'value) :explicit]]
         (let [global-predicate
               (function/lam
                [['input 'A]]
                (target-equality
                 'B (function/app 'mapping 'input) 'value))
               restricted-predicate
               (function/lam
                [['candidate 'A]]
                (proposition/conjunction
                 (function/app source 'candidate)
                 (target-equality
                  'B (function/app 'mapping 'candidate) 'value)))
               restricted-result
               (proposition/existence
                data-level 'A restricted-predicate)]
           (function/app
            (function/const* 'proposition/use-witness [data-level])
            'A global-predicate restricted-result
            (function/app 'surjection 'value)
            (function/lam
             [['input 'A]
              ['image-equality
               (target-equality 'B (function/app 'mapping 'input) 'value)]]
             (function/app
              (function/const* 'proposition/witness [data-level])
              'A restricted-predicate 'input
              (function/app
               (function/const* 'proposition/conjoin [])
               (function/app source 'input)
               (target-equality 'B (function/app 'mapping 'input) 'value)
               (function/app
                (function/const* 'equality/reverse-substitution
                                 [target-data-level])
                'B (function/app 'mapping 'input) 'value 'image-equality
                'target 'target-member)
               'image-equality))))))]
    {:name 'set/finite-of-preimage-under-surjection
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['target set-b :implicit]
       ['preimage-finite (finite 'A source) :explicit]
       ['surjection global-surjection :explicit]]
      (target-finite 'B 'target))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['mapping (function/arrow 'A 'B) :implicit]
       ['target set-b :implicit]
       ['preimage-finite (finite 'A source) :explicit]
       ['surjection global-surjection :explicit]]
      (function/app
       (function/const* 'set/finite-of-surjection [U V])
       'A 'B source 'target 'mapping
       restricted-surjection 'preimage-finite))}))

(def finite-of-product-left-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        product (product-type 'A 'B)
        product-set-value (product-set 'A 'B 'left 'right)
        fst-mapping
        (function/lam
         [['pair product]]
         (first-value 'A 'B 'pair))
        result (finite 'A 'left)]
    {:name 'set/finite-of-product-left
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['product-finite
        (product-finite 'A 'B product-set-value) :explicit]
       ['right-nonempty (target-nonempty 'B 'right) :explicit]]
      result)
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['product-finite
        (product-finite 'A 'B product-set-value) :explicit]
       ['right-nonempty (target-nonempty 'B 'right) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [target-data-level])
       'B 'right result 'right-nonempty
       (function/lam
        [['right-value 'B]
         ['right-member (function/app 'right 'right-value)]]
        (let [surjection
              (function/lam
               [['value 'A :implicit]
                ['left-member (function/app 'left 'value) :explicit]]
               (let [pair (pair-value 'A 'B 'value 'right-value)
                     member
                     (proposition/conjunction
                      (function/app 'left 'value)
                      (function/app 'right 'right-value))]
                 (function/app
                  (function/const* 'proposition/witness [product-data-level])
                  product
                  (function/lam
                   [['candidate product]]
                   (proposition/conjunction
                    (function/app product-set-value 'candidate)
                    (equality 'A
                              (first-value 'A 'B 'candidate) 'value)))
                  pair
                  (function/app
                   (function/const* 'proposition/conjoin [])
                   member
                   (equality 'A (first-value 'A 'B pair) 'value)
                   (function/app
                    (function/const* 'proposition/conjoin [])
                    (function/app 'left 'value)
                    (function/app 'right 'right-value)
                    'left-member 'right-member)
                   (function/app
                    (function/const* 'equality/reflexive [data-level])
                    'A 'value)))))]
          (function/app
           (function/const* 'set/finite-of-surjection [product-level U])
           product 'A product-set-value 'left fst-mapping
           surjection 'product-finite)))))}))

(def finite-of-product-right-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        product (product-type 'A 'B)
        product-set-value (product-set 'A 'B 'left 'right)
        snd-mapping
        (function/lam
         [['pair product]]
         (second-value 'A 'B 'pair))
        result (target-finite 'B 'right)]
    {:name 'set/finite-of-product-right
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['product-finite
        (product-finite 'A 'B product-set-value) :explicit]
       ['left-nonempty (nonempty 'A 'left) :explicit]]
      result)
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['product-finite
        (product-finite 'A 'B product-set-value) :explicit]
       ['left-nonempty (nonempty 'A 'left) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A 'left result 'left-nonempty
       (function/lam
        [['left-value 'A]
         ['left-member (function/app 'left 'left-value)]]
        (let [surjection
              (function/lam
               [['value 'B :implicit]
                ['right-member (function/app 'right 'value) :explicit]]
               (let [pair (pair-value 'A 'B 'left-value 'value)
                     member
                     (proposition/conjunction
                      (function/app 'left 'left-value)
                      (function/app 'right 'value))]
                 (function/app
                  (function/const* 'proposition/witness [product-data-level])
                  product
                  (function/lam
                   [['candidate product]]
                   (proposition/conjunction
                    (function/app product-set-value 'candidate)
                    (target-equality
                     'B (second-value 'A 'B 'candidate) 'value)))
                  pair
                  (function/app
                   (function/const* 'proposition/conjoin [])
                   member
                   (target-equality
                    'B (second-value 'A 'B pair) 'value)
                   (function/app
                    (function/const* 'proposition/conjoin [])
                    (function/app 'left 'left-value)
                    (function/app 'right 'value)
                    'left-member 'right-member)
                   (function/app
                    (function/const* 'equality/reflexive
                                     [target-data-level])
                    'B 'value)))))]
          (function/app
           (function/const* 'set/finite-of-surjection [product-level V])
           product 'B product-set-value 'right snd-mapping
           surjection 'product-finite)))))}))

(def infinite-product-left-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        product-set-value (product-set 'A 'B 'left 'right)]
    {:name 'set/infinite-product-left
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['left-infinite (infinite 'A 'left) :explicit]
       ['right-nonempty (target-nonempty 'B 'right) :explicit]]
      (function/app (function/const* 'set/infinite [product-level])
                    (product-type 'A 'B) product-set-value))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['left-infinite (infinite 'A 'left) :explicit]
       ['right-nonempty (target-nonempty 'B 'right) :explicit]
       ['product-finite
        (product-finite 'A 'B product-set-value)]]
      (function/app
       'left-infinite
       (function/app
        (function/const* 'set/finite-of-product-left [U V])
        'A 'B 'left 'right 'product-finite 'right-nonempty)))}))

(def infinite-product-right-spec
  (let [set-a (set-of 'A)
        set-b (target-set-of 'B)
        product-set-value (product-set 'A 'B 'left 'right)]
    {:name 'set/infinite-product-right
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['right-infinite (target-infinite 'B 'right) :explicit]
       ['left-nonempty (nonempty 'A 'left) :explicit]]
      (function/app (function/const* 'set/infinite [product-level])
                    (product-type 'A 'B) product-set-value))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['left set-a :implicit] ['right set-b :implicit]
       ['right-infinite (target-infinite 'B 'right) :explicit]
       ['left-nonempty (nonempty 'A 'left) :explicit]
       ['product-finite
        (product-finite 'A 'B product-set-value)]]
      (function/app
       'right-infinite
       (function/app
        (function/const* 'set/finite-of-product-right [U V])
        'A 'B 'left 'right 'product-finite 'left-nonempty)))}))

(def definition-specs [product-map-list-spec])

(def theorem-specs
  [membership-append-left-spec membership-append-right-spec
   cover-cons-spec cover-append-spec finite-insert-spec finite-union-spec
   finite-subset-spec finite-insert-equivalence-spec
   finite-union-equivalence-spec membership-map-spec
   membership-product-map-spec cover-image-spec finite-image-spec
   product-eta-spec cover-image2-spec finite-image2-spec
   cover-product-spec finite-product-spec finite-of-surjection-spec
   infinite-mono-spec infinite-of-image-spec finite-seq-spec
   finite-of-preimage-under-surjection-spec
   finite-of-product-left-spec finite-of-product-right-spec
   infinite-product-left-spec infinite-product-right-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-set theorem failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (or (:kind spec) :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :constructive-finite-set-theorems}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-set declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.set))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
