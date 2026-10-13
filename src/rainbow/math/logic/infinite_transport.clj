(ns rainbow.math.logic.infinite-transport
  "Sort-polymorphic infinitude transport and a faithful native Int model."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def L [:param 'l])
(def M [:param 'm])
(def sort-l [:sort L])
(def sort-m [:sort M])
(def nat (function/const* 'data/Nat []))
(def int-type (function/const* 'data/Int []))

(defn int-spec [checked-environment]
  (let [nat-id (environment/resolve-id checked-environment 'data/Nat)]
    {:block/schema-version 1
     :block/alias 'data/Int
     :block/universes []
     :block/parameters []
     :block/sort-level type-level
     :block/constructors
     [{:constructor/alias 'int/of-nat
       :constructor/fields
       [{:field/name 'magnitude :field/type [:const nat-id []]}]}
      {:constructor/alias 'int/negative-successor
       :constructor/fields
       [{:field/name 'magnitude :field/type [:const nat-id []]}]}]}))

(def constant-aliases
  {"Int" 'data/Int
   "Int.ofNat" 'int/of-nat
   "Int.negSucc" 'int/negative-successor
   "Int.rec" 'data/Int.rec})

(defn- list-of [level carrier]
  (finite-type/list-of level carrier))

(defn- membership [level carrier enumeration value]
  (finite-type/membership level carrier enumeration value))

(defn- finite [level carrier]
  (finite-type/finite level carrier))

(defn- infinite [level carrier]
  (finite-type/infinite level carrier))

(defn- map-list [source-level target-level source target mapping enumeration]
  (function/app (function/const* 'list/map [source-level target-level])
                source target mapping enumeration))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(def int-to-nat-spec
  {:name 'int/to-nat
   :kind :definition
   :universes []
   :type (function/arrow int-type nat)
   :value
   (function/lam
    [['value int-type]]
    (function/app
     (function/const* 'data/Int.rec [type-level])
     (function/lam [['ignored int-type]] nat)
     (function/lam [['magnitude nat]] 'magnitude)
     (function/lam [['magnitude nat]] 'magnitude)
     'value))})

(def definition-specs [int-to-nat-spec])

(def sort-membership-map-spec
  (let [list-a (list-of L 'A)
        nil-a (function/app (function/const* 'data/nil [L]) 'A)
        nil-b (function/app (function/const* 'data/nil [M]) 'B)
        mapped (fn [enumeration]
                 (map-list L M 'A 'B 'mapping enumeration))
        motive
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A]
           ['member (membership L 'A 'enumeration 'value)]]
          (membership M 'B (mapped 'enumeration)
                      (function/app 'mapping 'value))))]
    {:name 'list/sort-membership-map
     :universes ['l 'm]
     :type
     (function/forall
      [['A sort-l] ['B sort-m]
       ['mapping (function/arrow 'A 'B)]
       ['enumeration list-a] ['value 'A]
       ['member (membership L 'A 'enumeration 'value)]]
      (membership M 'B (mapped 'enumeration)
                  (function/app 'mapping 'value)))
     :value
     (function/lam
      [['A sort-l] ['B sort-m] ['mapping (function/arrow 'A 'B)]
       ['enumeration list-a]]
      (function/app
       (function/const* 'data/List.rec [L zero-level])
       'A motive
       (function/lam
        [['value 'A] ['impossible (membership L 'A nil-a 'value)]]
        (function/app
         (function/const* 'proposition/explode [])
         (membership M 'B nil-b (function/app 'mapping 'value))
         'impossible))
       (function/lam
        [['head 'A] ['tail list-a]
         ['induction-hypothesis (function/app motive 'tail)]
         ['value 'A]
         ['member
          (membership
           L 'A
           (function/app (function/const* 'data/cons [L])
                         'A 'head 'tail)
           'value)]]
        (let [source-head (equality L 'A 'value 'head)
              source-tail (membership L 'A 'tail 'value)
              target-head
              (equality M 'B (function/app 'mapping 'value)
                        (function/app 'mapping 'head))
              target-tail
              (membership M 'B (mapped 'tail)
                          (function/app 'mapping 'value))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           source-head source-tail
           (proposition/disjunction target-head target-tail)
           'member
           (function/lam
            [['at-head source-head]]
            (function/app
             (function/const* 'proposition/left-disjunct [])
             target-head target-tail
             (function/app
              (function/const* 'equality/congruent-function [L M])
              'A 'B 'mapping 'value 'head 'at-head)))
           (function/lam
            [['in-tail source-tail]]
            (function/app
             (function/const* 'proposition/right-disjunct [])
             target-head target-tail
             (function/app 'induction-hypothesis 'value 'in-tail))))))
       'enumeration))}))

(def finite-of-surjection-spec
  (let [list-a (list-of L 'A)
        list-b (list-of M 'B)
        mapped (fn [enumeration]
                 (map-list L M 'A 'B 'mapping enumeration))
        cover-a
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A]] (membership L 'A 'enumeration 'value)))
        cover-b
        (function/lam
         [['enumeration list-b]]
         (function/forall
          [['value 'B]] (membership M 'B 'enumeration 'value)))
        surjective
        (function/surjective L M 'A 'B 'mapping)]
    {:name 'type/finite-of-surjection
     :universes ['l 'm]
     :type
     (function/forall
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['onto surjective :explicit]
       ['source-finite (finite L 'A) :explicit]]
      (finite M 'B))
     :value
     (function/lam
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['onto surjective :explicit]
       ['source-finite (finite L 'A) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [L])
       list-a cover-a (finite M 'B) 'source-finite
       (function/lam
        [['enumeration list-a]
         ['source-cover (function/app cover-a 'enumeration)]]
        (let [target-enumeration (mapped 'enumeration)]
          (witness
           M list-b cover-b target-enumeration
           (function/lam
            [['target 'B]]
            (let [fiber
                  (function/lam
                   [['source 'A]]
                   (equality M 'B (function/app 'mapping 'source) 'target))
                  target-member
                  (membership M 'B target-enumeration 'target)]
              (function/app
               (function/const* 'proposition/use-witness [L])
               'A fiber target-member (function/app 'onto 'target)
               (function/lam
                [['source 'A]
                 ['same
                  (equality M 'B (function/app 'mapping 'source) 'target)]]
                (function/app
                 'same
                 (function/lam
                  [['candidate 'B]]
                  (membership M 'B target-enumeration 'candidate))
                 (function/app
                  (function/const* 'list/sort-membership-map [L M])
                  'A 'B 'mapping 'enumeration 'source
                  (function/app 'source-cover 'source))))))))))))}))

(def infinite-of-surjection-spec
  (let [source-infinite (infinite L 'A)
        target-infinite (infinite M 'B)
        surjective (function/surjective L M 'A 'B 'mapping)]
    {:name 'type/infinite-of-surjection
     :universes ['l 'm]
     :type
     (function/forall
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['target-infinite target-infinite :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['onto surjective :explicit]]
      source-infinite)
     :value
     (function/lam
      [['A sort-l :implicit] ['B sort-m :implicit]
       ['target-infinite target-infinite :implicit]
       ['mapping (function/arrow 'A 'B) :explicit]
       ['onto surjective :explicit]
       ['source-finite (finite L 'A)]]
      (function/app
       'target-infinite
       (function/app
        (function/const* 'type/finite-of-surjection [L M])
        'A 'B 'mapping 'onto 'source-finite)))}))

(def int-to-nat-surjective-spec
  (let [mapping (function/const* 'int/to-nat [])
        onto (function/surjective type-level type-level
                                   int-type nat mapping)]
    {:name 'int/to-nat-surjective
     :universes []
     :type onto
     :value
     (function/lam
      [['target nat]]
      (witness
       type-level int-type
       (function/lam
        [['source int-type]]
        (equality type-level nat (function/app mapping 'source) 'target))
       (function/app (function/const* 'int/of-nat []) 'target)
       (function/app (function/const* 'equality/reflexive [type-level])
                     nat 'target)))}))

(def infinite-int-spec
  (let [mapping (function/const* 'int/to-nat [])]
    {:name 'type/infinite-int
     :universes []
     :type (infinite type-level int-type)
     :value
     (function/app
      (function/const* 'type/infinite-of-surjection
                       [type-level type-level])
      int-type nat
      (function/const* 'type/infinite-nat [])
      mapping
      (function/const* 'int/to-nat-surjective []))}))

(def theorem-specs
  [sort-membership-map-spec finite-of-surjection-spec
   infinite-of-surjection-spec int-to-nat-surjective-spec infinite-int-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Infinite-transport expression failed elaboration"
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
          :rainbow/transparency (if (= :definition (:kind spec))
                                  :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :sort-polymorphic-infinite-transport}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Infinite-transport declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (let [added (kernel/add-inductive-block checked-environment
                                          (int-spec checked-environment))]
    (when-not (= :accepted (:status added))
      (throw (ex-info "Native Int inductive block was rejected"
                      {:result added})))
    (reduce add-spec (:environment added)
            (concat definition-specs theorem-specs))))

(defn inductive-ids [checked-environment]
  (into (sorted-map)
        (map (fn [name]
               [name (environment/resolve-id checked-environment name)]))
        ['data/Int 'int/of-nat 'int/negative-successor 'data/Int.rec]))

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
