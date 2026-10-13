(ns rainbow.math.logic.fintype
  "Finite carrier data as an extensional complete native Finset."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero [:zero])
(def one [:succ zero])
(def U finite-set/U)
(def data-level finite-set/data-level)
(def type-u finite-set/type-u)

(defn- set-of [carrier]
  (finite-set/set-of carrier))

(defn- finset-of [carrier]
  (function/app (function/const* 'finset/Finset [U]) carrier))

(defn- finset-set [carrier source]
  (function/app (function/const* 'finset/to-set [U]) carrier source))

(defn- finite-set [carrier source]
  (finite-set/finite carrier source))

(defn- type-finite [carrier]
  (finite-type/finite data-level carrier))

(defn- type-infinite [carrier]
  (finite-type/infinite data-level carrier))

(defn- universal [carrier]
  (function/app (function/const* 'set/universal [U]) carrier))

(defn- completeness-predicate [carrier]
  (function/lam
   [['elements (finset-of carrier)]]
   (function/forall
    [['value carrier]]
    (function/app (finset-set carrier 'elements) 'value))))

(defn- fintype-of [carrier]
  (function/app (function/const* 'fintype/Fintype [U]) carrier))

(defn- elements [carrier instance]
  (function/app (function/const* 'fintype/elements [U]) carrier instance))

(defn- complete [carrier instance value]
  (function/app (function/const* 'fintype/complete [U])
                carrier instance value))

(defn- nonempty [level carrier]
  (function/app (function/const* 'proposition/nonempty [level]) carrier))

(defn- is-empty [level carrier]
  (function/app (function/const* 'proposition/is-empty [level]) carrier))

(defn- equality [carrier left right]
  (function/app (function/const* 'equality/Eq [data-level])
                carrier left right))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- subtype-of-set [carrier source]
  (function/app (function/const* 'data/Subtype [data-level])
                carrier source))

(def fintype-spec
  {:name 'fintype/Fintype
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type (function/forall [['A type-u]] type-u)
   :value
   (function/lam
    [['A type-u]]
    (function/app (function/const* 'data/Subtype [data-level])
                  (finset-of 'A) (completeness-predicate 'A)))})

(def elements-spec
  {:name 'fintype/elements
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['instance (fintype-of 'A)]] (finset-of 'A))
   :value
   (function/lam
    [['A type-u] ['instance (fintype-of 'A)]]
    (function/app (function/const* 'subtype/value [data-level])
                  (finset-of 'A) (completeness-predicate 'A) 'instance))})

(def complete-spec
  {:name 'fintype/complete
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['instance (fintype-of 'A)] ['value 'A]]
    (function/app (finset-set 'A (elements 'A 'instance)) 'value))
   :value
   (function/lam
    [['A type-u] ['instance (fintype-of 'A)]]
    (function/app (function/const* 'subtype/property [data-level])
                  (finset-of 'A) (completeness-predicate 'A) 'instance))})

(def from-finite-spec
  (let [finset-a (finset-of 'A)
        universal-a (universal 'A)
        universal-finite (finite-set 'A universal-a)
        all-elements
        (fn [finite-evidence]
          (function/app
           (function/const* 'data/subtype [data-level])
           (set-of 'A)
           (function/lam [['source (set-of 'A)]] (finite-set 'A 'source))
           universal-a finite-evidence))]
    {:name 'fintype/from-finite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['finite-evidence (type-finite 'A) :explicit]]
      (fintype-of 'A))
     :value
     (function/lam
      [['A type-u :implicit] ['finite-evidence (type-finite 'A) :explicit]]
      (let [universal-finite-evidence
            (proposition/backward-equivalence
             universal-finite (type-finite 'A)
             (function/app
              (function/const* 'type/finite-universal-equivalence [U]) 'A)
             'finite-evidence)]
        (function/app
         (function/const* 'data/subtype [data-level])
         finset-a (completeness-predicate 'A)
         (all-elements universal-finite-evidence)
         (function/lam
          [['value 'A]] (function/const* 'proposition/trivial [])))))}))

(def to-finite-spec
  (let [universal-a (universal 'A)
        element-set (finset-set 'A (elements 'A 'instance))
        universal-finite (finite-set 'A universal-a)]
    {:name 'fintype/to-finite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['instance (fintype-of 'A) :explicit]]
      (type-finite 'A))
     :value
     (function/lam
      [['A type-u :implicit] ['instance (fintype-of 'A) :explicit]]
      (function/app
       (function/const* 'type/finite-of-finite-universal [U]) 'A
       (function/app
        (function/const* 'set/finite-subset-preserved [U])
        'A universal-a element-set
        (function/lam
         [['value 'A]
          ['universal-member (function/app universal-a 'value)]]
         (complete 'A 'instance 'value))
        (function/app (function/const* 'finset/finite-evidence [U])
                      'A (elements 'A 'instance)))))}))

(def subsingleton-spec
  (let [fintype-a (fintype-of 'A)
        left-elements (elements 'A 'left)
        right-elements (elements 'A 'right)]
    {:name 'fintype/subsingleton
     :universes ['u]
     :type
     (function/forall
      [['A type-u :explicit]]
      (function/app (function/const* 'type/subsingleton [data-level])
                    fintype-a))
     :value
     (function/lam
      [['A type-u :explicit] ['left fintype-a] ['right fintype-a]]
      (function/app
       (function/const* 'subtype/extensional [U])
       (finset-of 'A) (completeness-predicate 'A) 'left 'right
       (function/app
        (function/const* 'finset/extensional [U])
        'A left-elements right-elements
        (function/lam
         [['value 'A]]
         (let [left-member (function/app (finset-set 'A left-elements) 'value)
               right-member
               (function/app (finset-set 'A right-elements) 'value)]
           (function/app
            (function/const* 'proposition/equivalence-intro [])
            left-member right-member
            (function/lam [['ignored left-member]]
                          (complete 'A 'right 'value))
            (function/lam [['ignored right-member]]
                          (complete 'A 'left 'value))))))))}))

(def finite-equivalent-nonempty-spec
  (let [finite-a (type-finite 'A)
        fintype-a (fintype-of 'A)
        inhabited (nonempty data-level fintype-a)]
    {:name 'fintype/finite-equivalent-nonempty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :explicit]]
      (proposition/equivalence finite-a inhabited))
     :value
     (function/lam
      [['A type-u :explicit]]
      (proposition/introduce-equivalence
       finite-a inhabited
       (function/lam
        [['finite-evidence finite-a]]
        (function/app
         (function/const* 'proposition/nonempty-intro [data-level])
         fintype-a
         (function/app (function/const* 'fintype/from-finite [U])
                       'A 'finite-evidence)))
       (function/lam
        [['inhabited inhabited]]
        (function/app
         'inhabited finite-a
         (function/lam
          [['instance fintype-a]]
          (function/app (function/const* 'fintype/to-finite [U])
                        'A 'instance))))))}))

(def is-empty-equivalent-infinite-spec
  (let [fintype-a (fintype-of 'A)
        empty-fintype (is-empty data-level fintype-a)
        infinite-a (type-infinite 'A)]
    {:name 'fintype/is-empty-equivalent-infinite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (proposition/equivalence empty-fintype infinite-a))
     :value
     (function/lam
      [['A type-u :implicit]]
      (proposition/introduce-equivalence
       empty-fintype infinite-a
       (function/lam
        [['empty empty-fintype] ['finite-evidence (type-finite 'A)]]
        (function/app
         'empty
         (function/app (function/const* 'fintype/from-finite [U])
                       'A 'finite-evidence)))
       (function/lam
        [['infinite infinite-a] ['instance fintype-a]]
        (function/app
         'infinite
         (function/app (function/const* 'fintype/to-finite [U])
                       'A 'instance)))))}))

(def infinite-of-is-empty-spec
  (let [fintype-a (fintype-of 'A)
        empty-fintype (is-empty data-level fintype-a)
        infinite-a (type-infinite 'A)]
    {:name 'fintype/infinite-of-is-empty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['empty empty-fintype :explicit]] infinite-a)
     :value
     (function/lam
      [['A type-u :implicit] ['empty empty-fintype :explicit]]
      (proposition/forward-equivalence
       empty-fintype infinite-a
       (function/app
        (function/const* 'fintype/is-empty-equivalent-infinite [U]) 'A)
       'empty))}))

(def is-empty-proposition-equality-spec
  (let [left (is-empty data-level (fintype-of 'A))
        right (type-infinite 'A)]
    {:name 'fintype/is-empty-proposition-equality
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
        (function/const* 'fintype/is-empty-equivalent-infinite [U]) 'A)))}))

(def set-finite-nonempty-fintype-spec
  (let [element (subtype-of-set 'A 'source)
        source-finite (finite-set 'A 'source)
        element-finite (type-finite element)
        fintype-element (fintype-of element)
        inhabited (nonempty data-level fintype-element)]
    {:name 'set/finite-to-nonempty-fintype
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source (set-of 'A) :implicit]
       ['finite-evidence source-finite :explicit]]
      inhabited)
     :value
     (function/lam
      [['A type-u :implicit] ['source (set-of 'A) :implicit]
       ['finite-evidence source-finite :explicit]]
      (let [element-finite-evidence
            (proposition/forward-equivalence
             source-finite element-finite
             (function/app
              (function/const* 'set/finite-subtype-equivalence [U])
              'A 'source)
             'finite-evidence)]
        (function/app
         (function/const* 'proposition/nonempty-intro [data-level])
         fintype-element
         (function/app (function/const* 'fintype/from-finite [U])
                       element element-finite-evidence))))}))

(def universal-finite-equivalent-nonempty-fintype-spec
  (let [universal-finite (finite-set 'A (universal 'A))
        finite-a (type-finite 'A)
        inhabited (nonempty data-level (fintype-of 'A))]
    {:name 'set/universal-finite-equivalent-nonempty-fintype
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (proposition/equivalence universal-finite inhabited))
     :value
     (function/lam
      [['A type-u :implicit]]
      (proposition/introduce-equivalence
       universal-finite inhabited
       (function/lam
        [['finite-universal universal-finite]]
        (proposition/forward-equivalence
         finite-a inhabited
         (function/app
          (function/const* 'fintype/finite-equivalent-nonempty [U]) 'A)
         (proposition/forward-equivalence
          universal-finite finite-a
          (function/app
           (function/const* 'type/finite-universal-equivalence [U]) 'A)
          'finite-universal)))
       (function/lam
        [['inhabited inhabited]]
        (proposition/backward-equivalence
         universal-finite finite-a
         (function/app
          (function/const* 'type/finite-universal-equivalence [U]) 'A)
         (proposition/backward-equivalence
          finite-a inhabited
          (function/app
           (function/const* 'fintype/finite-equivalent-nonempty [U]) 'A)
          'inhabited)))))}))

(def set-finite-equivalent-subtype-fintype-spec
  (let [element (subtype-of-set 'A 'source)
        source-finite (finite-set 'A 'source)
        element-finite (type-finite element)
        inhabited (nonempty data-level (fintype-of element))]
    {:name 'set/finite-equivalent-subtype-fintype
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source (set-of 'A) :implicit]]
      (proposition/equivalence source-finite inhabited))
     :value
     (function/lam
      [['A type-u :implicit] ['source (set-of 'A) :implicit]]
      (proposition/introduce-equivalence
       source-finite inhabited
       (function/lam
        [['finite-evidence source-finite]]
        (proposition/forward-equivalence
         element-finite inhabited
         (function/app
          (function/const* 'fintype/finite-equivalent-nonempty [U]) element)
         (proposition/forward-equivalence
          source-finite element-finite
          (function/app
           (function/const* 'set/finite-subtype-equivalence [U])
           'A 'source)
          'finite-evidence)))
       (function/lam
        [['inhabited inhabited]]
        (proposition/backward-equivalence
         source-finite element-finite
         (function/app
          (function/const* 'set/finite-subtype-equivalence [U])
          'A 'source)
         (proposition/backward-equivalence
          element-finite inhabited
          (function/app
           (function/const* 'fintype/finite-equivalent-nonempty [U]) element)
          'inhabited)))))}))

(def constant-aliases {"Fintype" 'fintype/Fintype})

(def definition-specs [fintype-spec elements-spec complete-spec])

(def theorem-specs
  [from-finite-spec to-finite-spec subsingleton-spec
   finite-equivalent-nonempty-spec is-empty-equivalent-infinite-spec
   infinite-of-is-empty-spec is-empty-proposition-equality-spec
   set-finite-nonempty-fintype-spec
   universal-finite-equivalent-nonempty-fintype-spec
   set-finite-equivalent-subtype-fintype-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Fintype expression failed elaboration"
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
          {:origin :native :producer :extensional-complete-finset-fintype}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Fintype declaration was rejected"
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
