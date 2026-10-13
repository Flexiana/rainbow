(ns rainbow.math.logic.finset
  "Extensional bundled finite sets as native Clojure proof data."
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

(defn- finite [element source]
  (finite-set/finite element source))

(defn- set-nonempty [element source]
  (finite-set/nonempty element source))

(defn- membership [element enumeration value]
  (finite-set/membership element enumeration value))

(defn- equality [carrier left right]
  (function/equality data-level carrier left right))

(defn- finset-predicate [element]
  (function/lam
   [['source (set-of element)]]
   (finite element 'source)))

(defn- finset-of [element]
  (function/app (function/const* 'finset/Finset [U]) element))

(defn- to-set [element source]
  (function/app (function/const* 'finset/to-set [U]) element source))

(defn- empty-finset [element]
  (function/app (function/const* 'finset/empty [U]) element))

(defn- singleton-finset [element selected]
  (function/app (function/const* 'finset/singleton [U])
                element selected))

(defn- subset [element left right]
  (function/app (function/const* 'finset/subset [U])
                element left right))

(defn- nonempty [element source]
  (function/app (function/const* 'finset/nonempty [U])
                element source))

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

(def finset-type-spec
  (let [set-a (set-of 'A)]
    {:name 'finset/Finset
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type (function/forall [['A type-u]] type-u)
     :value
     (function/lam
      [['A type-u]]
      (function/app (function/const* 'data/Subtype [data-level])
                    set-a (finset-predicate 'A)))}))

(def to-set-spec
  {:name 'finset/to-set
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (finset-of 'A)]] (set-of 'A))
   :value
   (function/lam
    [['A type-u] ['source (finset-of 'A)]]
    (function/app (function/const* 'subtype/value [data-level])
                  (set-of 'A) (finset-predicate 'A) 'source))})

(def finite-evidence-spec
  {:name 'finset/finite-evidence
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (finset-of 'A)]]
    (finite 'A (to-set 'A 'source)))
   :value
   (function/lam
    [['A type-u] ['source (finset-of 'A)]]
    (function/app (function/const* 'subtype/property [data-level])
                  (set-of 'A) (finset-predicate 'A) 'source))})

(def empty-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        empty-set (function/app (function/const* 'set/empty [U]) 'A)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        cover
        (function/lam
         [['enumeration list-a]]
         (finite-set/cover 'A empty-set 'enumeration))
        finite-empty
        (witness
         data-level list-a cover nil-a
         (function/lam
          [['value 'A] ['impossible (function/app empty-set 'value)]]
          (explode (membership 'A nil-a 'value) 'impossible)))]
    {:name 'finset/empty
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type (function/forall [['A type-u]] (finset-of 'A))
     :value
     (function/lam
      [['A type-u]]
      (function/app (function/const* 'data/subtype [data-level])
                    set-a (finset-predicate 'A) empty-set finite-empty))}))

(def subset-spec
  {:name 'finset/subset
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]]
    (function/arrow (finset-of 'A) (finset-of 'A) 'Prop))
   :value
   (function/lam
    [['A type-u] ['left (finset-of 'A)] ['right (finset-of 'A)]]
    (function/app (function/const* 'set/subset [U])
                  'A (to-set 'A 'left) (to-set 'A 'right)))})

(def nonempty-spec
  {:name 'finset/nonempty
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]] (function/arrow (finset-of 'A) 'Prop))
   :value
   (function/lam
    [['A type-u] ['source (finset-of 'A)]]
    (set-nonempty 'A (to-set 'A 'source)))})

(def singleton-spec
  (let [set-a (set-of 'A)
        list-a (list-of 'A)
        singleton-set
        (function/app (function/const* 'set/singleton [U])
                      'A 'selected)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        enumeration
        (function/app (function/const* 'data/cons [data-level])
                      'A 'selected nil-a)
        cover
        (function/lam
         [['candidate-enumeration list-a]]
         (finite-set/cover 'A singleton-set 'candidate-enumeration))
        finite-singleton
        (witness
         data-level list-a cover enumeration
         (function/lam
          [['value 'A]
           ['same (function/app singleton-set 'value)]]
          (function/app
           (function/const* 'proposition/left-disjunct [])
           (equality 'A 'value 'selected)
           (membership 'A nil-a 'value) 'same)))]
    {:name 'finset/singleton
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u]] (function/arrow 'A (finset-of 'A)))
     :value
     (function/lam
      [['A type-u] ['selected 'A]]
      (function/app (function/const* 'data/subtype [data-level])
                    set-a (finset-predicate 'A)
                    singleton-set finite-singleton))}))

(def subset-reflexive-explicit-spec
  {:name 'finset/subset-reflexive-explicit
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit] ['source (finset-of 'A) :explicit]]
    (subset 'A 'source 'source))
   :value
   (function/lam
    [['A type-u :implicit] ['source (finset-of 'A) :explicit]
     ['value 'A] ['member (function/app (to-set 'A 'source) 'value)]]
    'member)})

(def subset-reflexive-implicit-spec
  {:name 'finset/subset-reflexive-implicit
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit] ['source (finset-of 'A) :implicit]]
    (subset 'A 'source 'source))
   :value
   (function/lam
    [['A type-u :implicit] ['source (finset-of 'A) :implicit]
     ['value 'A] ['member (function/app (to-set 'A 'source) 'value)]]
    'member)})

(def empty-subset-spec
  {:name 'finset/empty-subset
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit] ['source (finset-of 'A) :explicit]]
    (subset 'A (empty-finset 'A) 'source))
   :value
   (function/lam
    [['A type-u :implicit] ['source (finset-of 'A) :explicit]
     ['value 'A]
     ['impossible (function/app (to-set 'A (empty-finset 'A)) 'value)]]
    (explode (function/app (to-set 'A 'source) 'value) 'impossible))})

(def empty-not-nonempty-spec
  {:name 'finset/empty-not-nonempty
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit]]
    (proposition/negation (nonempty 'A (empty-finset 'A))))
   :value
   (function/lam
    [['A type-u :implicit]
     ['inhabited (nonempty 'A (empty-finset 'A))]]
    (function/app
     (function/const* 'proposition/use-witness [data-level])
     'A (to-set 'A (empty-finset 'A))
     (proposition/falsity) 'inhabited
     (function/lam
      [['value 'A]
       ['impossible
        (function/app (to-set 'A (empty-finset 'A)) 'value)]]
      'impossible)))})

(def empty-nonempty-proposition-equality-spec
  (let [left (nonempty 'A (empty-finset 'A))
        right (proposition/falsity)]
    {:name 'finset/empty-nonempty-proposition-equality
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (function/app (function/const* 'equality/Eq [one])
                    'Prop left right))
     :value
     (function/lam
      [['A type-u :implicit]]
      (function/app
       (function/const* 'logic/proposition-extensionality [])
       left right
       (function/app
        (function/const* 'proposition/equivalence-intro [])
        left right
        (function/lam
         [['inhabited left]]
         (function/app
          (function/const* 'finset/empty-not-nonempty [U])
          'A 'inhabited))
        (function/lam
         [['impossible right]]
         (explode left 'impossible)))))}))

(def singleton-nonempty-spec
  {:name 'finset/singleton-nonempty
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit] ['selected 'A :explicit]]
    (nonempty 'A (singleton-finset 'A 'selected)))
   :value
   (function/lam
    [['A type-u :implicit] ['selected 'A :explicit]]
    (witness
     data-level 'A (to-set 'A (singleton-finset 'A 'selected))
     'selected
     (function/app (function/const* 'equality/reflexive [data-level])
                   'A 'selected)))})

(def nonempty-to-type-spec
  {:name 'finset/nonempty-to-type
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit] ['source (finset-of 'A) :implicit]
     ['inhabited (nonempty 'A 'source) :explicit]]
    (function/app (function/const* 'proposition/nonempty [data-level]) 'A))
   :value
   (function/lam
    [['A type-u :implicit] ['source (finset-of 'A) :implicit]
     ['inhabited (nonempty 'A 'source) :explicit]]
    (function/app
     (function/const* 'proposition/use-witness [data-level])
     'A (to-set 'A 'source)
     (function/app (function/const* 'proposition/nonempty [data-level]) 'A)
     'inhabited
     (function/lam
      [['value 'A] ['ignored (function/app (to-set 'A 'source) 'value)]]
      (function/app
       (function/const* 'proposition/nonempty-intro [data-level])
       'A 'value))))})

(def extensional-spec
  (let [finset-a (finset-of 'A)
        left-set (to-set 'A 'left)
        right-set (to-set 'A 'right)
        pointwise
        (function/forall
         [['value 'A]]
         (proposition/equivalence
          (function/app left-set 'value)
          (function/app right-set 'value)))]
    {:name 'finset/extensional
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left finset-a :explicit] ['right finset-a :explicit]
       ['pointwise pointwise :explicit]]
      (equality finset-a 'left 'right))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left finset-a :explicit] ['right finset-a :explicit]
       ['pointwise pointwise :explicit]]
      (function/app
       (function/const* 'subtype/extensional [U])
       (set-of 'A) (finset-predicate 'A) 'left 'right
       (function/app
        (function/const* 'logic/function-extensionality [data-level one])
        'A 'Prop left-set right-set
        (function/lam
         [['value 'A]]
         (function/app
          (function/const* 'logic/proposition-extensionality [])
          (function/app left-set 'value)
          (function/app right-set 'value)
          (function/app 'pointwise 'value))))))}))

(def eq-empty-or-nonempty-spec
  (let [finset-a (finset-of 'A)
        source-nonempty (nonempty 'A 'source)
        source-equals-empty
        (equality finset-a 'source (empty-finset 'A))
        target (proposition/disjunction source-equals-empty source-nonempty)]
    {:name 'finset/eq-empty-or-nonempty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :explicit]] target)
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :explicit]]
      (function/app
       (function/const* 'logic/classical-cases []) source-nonempty target
       (function/lam
        [['inhabited source-nonempty]]
        (function/app
         (function/const* 'proposition/right-disjunct [])
         source-equals-empty source-nonempty 'inhabited))
       (function/lam
        [['not-inhabited (proposition/negation source-nonempty)]]
        (function/app
         (function/const* 'proposition/left-disjunct [])
         source-equals-empty source-nonempty
         (function/app
          (function/const* 'finset/extensional [U])
          'A 'source (empty-finset 'A)
          (function/lam
           [['value 'A]]
           (let [source-member (function/app (to-set 'A 'source) 'value)
                 empty-member
                 (function/app (to-set 'A (empty-finset 'A)) 'value)]
             (function/app
              (function/const* 'proposition/equivalence-intro [])
              source-member empty-member
              (function/lam
               [['member source-member]]
               (explode
                empty-member
                (function/app
                 'not-inhabited
                 (witness data-level 'A (to-set 'A 'source)
                          'value 'member))))
              (function/lam
               [['impossible empty-member]]
               (explode source-member 'impossible))))))))))}))

(def nonempty-not-equal-empty-spec
  (let [finset-a (finset-of 'A)
        source-nonempty (nonempty 'A 'source)
        same-empty (equality finset-a 'source (empty-finset 'A))]
    {:name 'finset/nonempty-not-equal-empty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :implicit]
       ['inhabited source-nonempty :explicit]]
      (proposition/negation same-empty))
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :implicit]
       ['inhabited source-nonempty :explicit]
       ['same-empty same-empty]]
      (function/app
       (function/const* 'finset/empty-not-nonempty [U]) 'A
       (proposition-forward
        source-nonempty (nonempty 'A (empty-finset 'A))
        (proposition-congruence
         finset-a
         (function/lam [['candidate finset-a]] (nonempty 'A 'candidate))
         'source (empty-finset 'A) 'same-empty)
        'inhabited)))}))

(def nonempty-of-not-equal-empty-spec
  (let [finset-a (finset-of 'A)
        source-nonempty (nonempty 'A 'source)
        same-empty (equality finset-a 'source (empty-finset 'A))]
    {:name 'finset/nonempty-of-not-equal-empty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :implicit]
       ['not-empty (proposition/negation same-empty) :explicit]]
      source-nonempty)
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :implicit]
       ['not-empty (proposition/negation same-empty) :explicit]]
      (function/app
       (function/const* 'proposition/use-disjunction [])
       same-empty source-nonempty source-nonempty
       (function/app (function/const* 'finset/eq-empty-or-nonempty [U])
                     'A 'source)
       (function/lam
        [['same same-empty]]
        (explode source-nonempty (function/app 'not-empty 'same)))
       (function/lam [['inhabited source-nonempty]] 'inhabited)))}))

(def nonempty-equivalent-not-empty-spec
  (let [finset-a (finset-of 'A)
        source-nonempty (nonempty 'A 'source)
        not-empty
        (proposition/negation
         (equality finset-a 'source (empty-finset 'A)))]
    {:name 'finset/nonempty-equivalent-not-empty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :implicit]]
      (proposition/equivalence source-nonempty not-empty))
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       source-nonempty not-empty
       (function/lam
        [['inhabited source-nonempty]]
        (function/app
         (function/const* 'finset/nonempty-not-equal-empty [U])
         'A 'source 'inhabited))
       (function/lam
        [['not-empty not-empty]]
        (function/app
         (function/const* 'finset/nonempty-of-not-equal-empty [U])
         'A 'source 'not-empty))))}))

(def is-empty-of-all-empty-spec
  (let [finset-a (finset-of 'A)
        all-empty
        (function/forall
         [['source finset-a]]
         (equality finset-a 'source (empty-finset 'A)))]
    {:name 'finset/is-empty-of-all-empty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['all-empty all-empty :explicit]]
      (function/app (function/const* 'proposition/is-empty [data-level]) 'A))
     :value
     (function/lam
      [['A type-u :implicit] ['all-empty all-empty :explicit]
       ['value 'A]]
      (function/app
       (function/app
        (function/const* 'finset/nonempty-not-equal-empty [U])
        'A (singleton-finset 'A 'value)
        (function/app (function/const* 'finset/singleton-nonempty [U])
                      'A 'value))
       (function/app 'all-empty (singleton-finset 'A 'value))))}))

(def singleton-injective-spec
  (let [finset-a (finset-of 'A)
        singleton-map
        (function/lam [['value 'A]] (singleton-finset 'A 'value))]
    {:name 'finset/singleton-injective
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (function/injective data-level data-level
                          'A finset-a singleton-map))
     :value
     (function/lam
      [['A type-u :implicit] ['left 'A] ['right 'A]
       ['same-singleton
        (equality finset-a
                  (singleton-finset 'A 'left)
                  (singleton-finset 'A 'right))]]
      (let [left-finset (singleton-finset 'A 'left)
            right-finset (singleton-finset 'A 'right)
            left-set (to-set 'A left-finset)
            right-set (to-set 'A right-finset)
            same-sets
            (function/app
             (function/const* 'equality/congruent-function
                              [data-level data-level])
             finset-a (set-of 'A)
             (function/lam [['source finset-a]] (to-set 'A 'source))
             left-finset right-finset 'same-singleton)
            same-membership
            (proposition-congruence
             (set-of 'A)
             (function/lam
              [['source (set-of 'A)]] (function/app 'source 'left))
             left-set right-set same-sets)]
        (proposition-forward
         (function/app left-set 'left)
         (function/app right-set 'left)
         same-membership
         (function/app (function/const* 'equality/reflexive [data-level])
                       'A 'left))))}))

(def constant-aliases
  {"Finset" 'finset/Finset
   "Finset.instEmptyCollection" 'finset/empty
   "Finset.instHasSubset" 'finset/subset
   "Finset.Nonempty" 'finset/nonempty
   "Finset.instSingleton" 'finset/singleton})

(def definition-specs
  [finset-type-spec to-set-spec finite-evidence-spec empty-spec subset-spec
   nonempty-spec singleton-spec])

(def theorem-specs
  [subset-reflexive-explicit-spec subset-reflexive-implicit-spec
   empty-subset-spec empty-not-nonempty-spec
   empty-nonempty-proposition-equality-spec singleton-nonempty-spec
   nonempty-to-type-spec extensional-spec eq-empty-or-nonempty-spec
   nonempty-not-equal-empty-spec nonempty-of-not-equal-empty-spec
   nonempty-equivalent-not-empty-spec is-empty-of-all-empty-spec
   singleton-injective-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finset expression failed elaboration"
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
          {:origin :native :producer :extensional-bundled-finset}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finset declaration was rejected"
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
