(ns rainbow.math.finite.powerset
  "Finite powersets, infinite suprema, and subtype projection injectivity."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero [:zero])
(def one [:succ zero])
(def U finite-set/U)
(def data-level finite-set/data-level)
(def type-u finite-set/type-u)

(defn- set-of [element]
  (finite-set/set-of element))

(defn- list-of [element]
  (finite-set/list-of element))

(defn- membership [element enumeration value]
  (finite-set/membership element enumeration value))

(defn- equality [element left right]
  (finite-set/equality element left right))

(defn- finite [element source]
  (finite-set/finite element source))

(defn- infinite [element source]
  (finite-set/infinite element source))

(defn- empty-set [element]
  (function/app (function/const* 'set/empty [U]) element))

(defn- singleton-set [element selected]
  (function/app (function/const* 'set/singleton [U]) element selected))

(defn- insert-set [element selected source]
  (function/app (function/const* 'set/insert [U])
                element selected source))

(defn- difference [element left right]
  (function/app (function/const* 'set/difference [U])
                element left right))

(defn- powerset [element source]
  (function/app (function/const* 'set/powerset [U]) element source))

(defn- supremum [element family]
  (function/app (function/const* 'set/supremum [U]) element family))

(defn- list-powerset [element enumeration]
  (function/app (function/const* 'list/set-powerset [U])
                element enumeration))

(defn- append [element left right]
  (function/app (function/const* 'list/append [data-level])
                element left right))

(defn- map-list [source target mapping enumeration]
  (function/app (function/const* 'list/map [data-level data-level])
                source target mapping enumeration))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- explode [target impossible]
  (function/app (function/const* 'proposition/explode [])
                target impossible))

(defn- proposition-congruence [carrier mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [data-level one])
   carrier 'Prop mapping left right same))

(defn- proposition-forward [left right same evidence]
  (function/app (function/const* 'equality/proposition-forward [])
                left right same evidence))

(defn- proposition-backward [left right same evidence]
  (function/app (function/const* 'equality/proposition-backward [])
                left right same evidence))

(defn- set-equality
  "Builds equality of two predicate sets from pointwise implications."
  [element left right forward backward]
  (let [left-member (function/app left 'point)
        right-member (function/app right 'point)]
    (function/app
     (function/const* 'logic/function-extensionality [data-level one])
     element 'Prop left right
     (function/lam
      [['point element]]
      (function/app
       (function/const* 'logic/proposition-extensionality [])
       left-member right-member
       (function/app
        (function/const* 'proposition/equivalence-intro [])
        left-member right-member
        (forward 'point left-member right-member)
        (backward 'point left-member right-member)))))))

(def list-powerset-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        list-set-a (list-of set-a)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        nil-sets
        (function/app (function/const* 'data/nil [data-level]) set-a)
        empty (empty-set 'A)
        singleton-empty
        (function/app (function/const* 'data/cons [data-level])
                      set-a empty nil-sets)
        motive (function/lam [['ignored list-a]] list-set-a)]
    {:name 'list/set-powerset
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u] ['enumeration list-a]] list-set-a)
     :value
     (function/lam
      [['A type-u] ['enumeration list-a]]
      (function/app
       (function/const* 'data/List.rec [data-level data-level])
       'A motive singleton-empty
       (function/lam
        [['head 'A] ['tail list-a] ['tail-powerset list-set-a]]
        (let [add-head
              (function/lam
               [['source set-a]]
               (insert-set 'A 'head 'source))]
          (append set-a 'tail-powerset
                  (map-list set-a set-a add-head 'tail-powerset))))
       'enumeration))}))

(def membership-powerset-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        list-set-a (list-of set-a)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        nil-sets
        (function/app (function/const* 'data/nil [data-level]) set-a)
        empty (empty-set 'A)
        target
        (fn [enumeration]
          (function/forall
           [['candidate set-a]
            ['covered
             (function/forall
              [['value 'A]
               ['candidate-member (function/app 'candidate 'value)]]
              (membership 'A enumeration 'value))]]
           (membership set-a (list-powerset 'A enumeration) 'candidate)))
        motive (function/lam [['enumeration list-a]] (target 'enumeration))
        base
        (function/lam
         [['candidate set-a]
          ['covered
           (function/forall
            [['value 'A]
             ['candidate-member (function/app 'candidate 'value)]]
            (membership 'A nil-a 'value))]]
         (let [same-empty
               (set-equality
                'A 'candidate empty
                (fn [point left-member right-member]
                  (function/lam
                   [['candidate-member left-member]]
                   (function/app 'covered point 'candidate-member)))
                (fn [_ left-member right-member]
                  (function/lam
                   [['impossible right-member]]
                   (explode left-member 'impossible))))]
           (function/app
            (function/const* 'proposition/left-disjunct [])
            (equality set-a 'candidate empty)
            (membership set-a nil-sets 'candidate)
            same-empty)))]
    {:name 'list/membership-set-powerset
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['enumeration list-a]
       ['candidate set-a]
       ['covered
        (function/forall
         [['value 'A]
          ['candidate-member (function/app 'candidate 'value)]]
         (membership 'A 'enumeration 'value))]]
      (membership set-a (list-powerset 'A 'enumeration) 'candidate))
     :value
     (function/lam
      [['A type-u] ['enumeration list-a]]
      (function/app
       (function/const* 'data/List.rec [data-level zero])
       'A motive base
       (function/lam
        [['head 'A] ['tail list-a]
         ['induction-hypothesis (target 'tail)]
         ['candidate set-a]
         ['covered
          (function/forall
           [['value 'A]
            ['candidate-member (function/app 'candidate 'value)]]
           (membership
            'A
            (function/app (function/const* 'data/cons [data-level])
                          'A 'head 'tail)
            'value))]]
        (let [tail-powerset (list-powerset 'A 'tail)
              add-head
              (function/lam
               [['source set-a]]
               (insert-set 'A 'head 'source))
              mapped-heads
              (map-list set-a set-a add-head tail-powerset)
              all-subsets (append set-a tail-powerset mapped-heads)
              at-head (function/app 'candidate 'head)]
          (function/app
           (function/const* 'logic/classical-cases [])
           at-head (membership set-a all-subsets 'candidate)
           (function/lam
            [['head-member at-head]]
            (let [head-singleton (singleton-set 'A 'head)
                  remainder (difference 'A 'candidate head-singleton)
                  remainder-cover
                  (function/lam
                   [['value 'A]
                    ['remainder-member
                     (function/app remainder 'value)]]
                   (let [candidate-value (function/app 'candidate 'value)
                         same (equality 'A 'value 'head)
                         tail-member (membership 'A 'tail 'value)
                         candidate-evidence
                         (function/app
                          (function/const* 'proposition/left [])
                          candidate-value
                          (proposition/negation same)
                          'remainder-member)
                         not-same
                         (function/app
                          (function/const* 'proposition/right [])
                          candidate-value
                          (proposition/negation same)
                          'remainder-member)]
                     (function/app
                      (function/const* 'proposition/use-disjunction [])
                      same tail-member tail-member
                      (function/app 'covered 'value candidate-evidence)
                      (function/lam
                       [['same-value same]]
                       (explode tail-member
                                (function/app not-same 'same-value)))
                      (function/lam
                       [['in-tail tail-member]] 'in-tail))))
                  remainder-in-tail
                  (function/app 'induction-hypothesis
                                remainder remainder-cover)
                  inserted (insert-set 'A 'head remainder)
                  inserted-in-map
                  (function/app
                   (function/const* 'list/membership-map [U U])
                   set-a set-a add-head tail-powerset remainder
                   remainder-in-tail)
                  inserted-in-all
                  (function/app
                   (function/const* 'list/membership-append-right [U])
                   set-a tail-powerset mapped-heads inserted
                   inserted-in-map)
                  inserted-equals-candidate
                  (set-equality
                   'A inserted 'candidate
                   (fn [point left-member right-member]
                     (let [same (equality 'A point 'head)
                           remainder-member (function/app remainder point)]
                       (function/lam
                        [['inserted-member left-member]]
                        (function/app
                         (function/const* 'proposition/use-disjunction [])
                         same remainder-member right-member
                         'inserted-member
                         (function/lam
                          [['same-point same]]
                          (let [same-propositions
                                (proposition-congruence
                                 'A 'candidate point 'head 'same-point)]
                            (proposition-backward
                             right-member at-head same-propositions
                             'head-member)))
                         (function/lam
                          [['in-remainder remainder-member]]
                          (function/app
                           (function/const* 'proposition/left [])
                           right-member
                           (proposition/negation same)
                           'in-remainder))))))
                   (fn [point left-member right-member]
                     (let [same (equality 'A point 'head)
                           remainder-member (function/app remainder point)]
                       (function/lam
                        [['candidate-member right-member]]
                        (function/app
                         (function/const* 'logic/classical-cases [])
                         same left-member
                         (function/lam
                          [['same-point same]]
                          (function/app
                           (function/const* 'proposition/left-disjunct [])
                           same remainder-member 'same-point))
                         (function/lam
                          [['not-same (proposition/negation same)]]
                          (function/app
                           (function/const* 'proposition/right-disjunct [])
                           same remainder-member
                           (function/app
                            (function/const* 'proposition/conjoin [])
                            right-member (proposition/negation same)
                            'candidate-member 'not-same))))))))
                  same-membership
                  (proposition-congruence
                   set-a
                   (function/lam
                    [['source set-a]]
                    (membership set-a all-subsets 'source))
                   inserted 'candidate inserted-equals-candidate)]
              (proposition-forward
               (membership set-a all-subsets inserted)
               (membership set-a all-subsets 'candidate)
               same-membership inserted-in-all)))
           (function/lam
            [['not-head (proposition/negation at-head)]]
            (let [tail-cover
                  (function/lam
                   [['value 'A]
                    ['candidate-member (function/app 'candidate 'value)]]
                   (let [same (equality 'A 'value 'head)
                         tail-member (membership 'A 'tail 'value)]
                     (function/app
                      (function/const* 'proposition/use-disjunction [])
                      same tail-member tail-member
                      (function/app 'covered 'value 'candidate-member)
                      (function/lam
                       [['same-value same]]
                       (let [same-propositions
                             (proposition-congruence
                              'A 'candidate 'value 'head 'same-value)]
                         (explode
                          tail-member
                          (function/app
                           'not-head
                           (proposition-forward
                            (function/app 'candidate 'value) at-head
                            same-propositions 'candidate-member)))))
                      (function/lam
                       [['in-tail tail-member]] 'in-tail))))
                  in-tail-powerset
                  (function/app 'induction-hypothesis
                                'candidate tail-cover)]
              (function/app
               (function/const* 'list/membership-append-left [U])
               set-a tail-powerset mapped-heads 'candidate
               in-tail-powerset))))))
       'enumeration))}))

(def finite-powerset-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        list-set-a (list-of set-a)
        source-cover
        (function/lam
         [['enumeration list-a]]
         (finite-set/cover 'A 'source 'enumeration))
        powerset-source (powerset 'A 'source)
        powerset-cover
        (function/lam
         [['enumeration list-set-a]]
         (finite-set/cover set-a powerset-source 'enumeration))]
    {:name 'set/finite-powerset
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :implicit]
       ['source-finite (finite 'A 'source) :explicit]]
      (finite set-a powerset-source))
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :implicit]
       ['source-finite (finite 'A 'source) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       list-a source-cover (finite set-a powerset-source)
       'source-finite
       (function/lam
        [['enumeration list-a]
         ['covers-source (function/app source-cover 'enumeration)]]
        (witness
         data-level list-set-a powerset-cover
         (list-powerset 'A 'enumeration)
         (function/lam
          [['candidate set-a]
           ['candidate-subset (function/app powerset-source 'candidate)]]
          (function/app
           (function/const* 'list/membership-set-powerset [U])
           'A 'enumeration 'candidate
           (function/lam
            [['value 'A]
             ['candidate-member (function/app 'candidate 'value)]]
            (function/app
             'covers-source 'value
             (function/app 'candidate-subset
                           'value 'candidate-member)))))))))}))

(def infinite-supremum-spec
  (let [set-a (set-of 'A)
        family-of-a (set-of set-a)
        joined (supremum 'A 'family)
        powerset-joined (powerset 'A joined)
        family-infinite (infinite set-a 'family)
        joined-infinite (infinite 'A joined)
        inclusion
        (function/lam
         [['source set-a]
          ['source-member (function/app 'family 'source)]
          ['value 'A]
          ['value-member (function/app 'source 'value)]]
         (witness
          data-level set-a
          (function/lam
           [['candidate set-a]]
           (proposition/conjunction
            (function/app 'family 'candidate)
            (function/app 'candidate 'value)))
          'source
          (function/app
           (function/const* 'proposition/conjoin [])
           (function/app 'family 'source)
           (function/app 'source 'value)
           'source-member 'value-member)))]
    {:name 'set/infinite-supremum
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['family family-of-a :implicit]
       ['family-infinite family-infinite :explicit]]
      joined-infinite)
     :value
     (function/lam
      [['A type-u :implicit] ['family family-of-a :implicit]
       ['family-infinite family-infinite :explicit]
       ['joined-finite (finite 'A joined)]]
      (function/app
       'family-infinite
       (function/app
        (function/const* 'set/finite-subset-preserved [U])
        set-a 'family powerset-joined inclusion
        (function/app
         (function/const* 'set/finite-powerset [U])
         'A joined 'joined-finite))))}))

(def subtype-value-injective-spec
  (let [set-a (set-of 'A)
        subtype
        (function/app (function/const* 'data/Subtype [data-level])
                      'A 'source)
        value-map
        (function/app (function/const* 'subtype/value [data-level])
                      'A 'source)]
    {:name 'subtype/value-injective
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :explicit]]
      (function/injective data-level data-level
                          subtype 'A value-map))
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :explicit]
       ['left subtype] ['right subtype]
       ['same-value
        (equality 'A
                  (function/app value-map 'left)
                  (function/app value-map 'right))]]
      (function/app
       (function/const* 'subtype/extensional [U])
       'A 'source 'left 'right 'same-value))}))

(def definition-specs [list-powerset-spec])
(def theorem-specs
  [membership-powerset-spec finite-powerset-spec infinite-supremum-spec
   subtype-value-injective-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-powerset expression failed elaboration"
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
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-powerset-enumeration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-powerset declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (into definition-specs theorem-specs)))

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
