(ns rainbow.math.finite.subtype
  "Finite propositions and finite-subtype bridges as checked proof data."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.finite.type :as finite-type]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero [:zero])
(def proposition-level [:succ zero])
(def U finite-set/U)
(def data-level finite-set/data-level)
(def type-u finite-set/type-u)
(def L [:param 'l])
(def sort-l [:sort L])

(def subsingleton-spec
  {:name 'type/subsingleton
   :kind :definition
   :universes ['l]
   :type (function/forall [['A sort-l]] 'Prop)
   :value
   (function/lam
    [['A sort-l]]
    (function/forall
     [['left 'A] ['right 'A]]
     (proposition/equality L 'A 'left 'right)))})

(def constant-aliases {"Subsingleton" 'type/subsingleton})

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- conjoin [left right left-evidence right-evidence]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-evidence right-evidence))

(defn- equality [level carrier left right]
  (function/app (function/const* 'equality/Eq [level])
                carrier left right))

(defn- universal [level carrier]
  (function/app (function/const* 'set/universal [level]) carrier))

(defn- subtype [carrier predicate]
  (function/app (function/const* 'data/Subtype [data-level])
                carrier predicate))

(defn- subtype-value [carrier predicate value]
  (function/app (function/const* 'subtype/value [data-level])
                carrier predicate value))

(defn- subtype-property [carrier predicate value]
  (function/app (function/const* 'subtype/property [data-level])
                carrier predicate value))

(defn- subtype-intro [carrier predicate value property]
  (function/app (function/const* 'data/subtype [data-level])
                carrier predicate value property))

;; type/finite-proposition (every proposition is finite, via a list of its proofs) was removed in 1.4.2. It
;; instantiated type/finite at Prop, whose membership eliminates data/List.{0} into Prop: large elimination
;; from a proposition with two constructors, which the kernel now refuses (with logic/proof-irrelevance it
;; derived False). Lean states the same fact for the type Prop through ULift/PLift, never List of proofs.

(def finite-of-subsingleton-spec
  (let [list-a (finite-type/list-of L 'A)
        nil-a (function/app (function/const* 'data/nil [L]) 'A)
        nonempty-a
        (function/app (function/const* 'proposition/nonempty [L]) 'A)
        cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A]]
          (finite-type/membership L 'A 'enumeration 'value)))
        target (finite-type/finite L 'A)]
    {:name 'type/finite-of-subsingleton
     :universes ['l]
     :type
     (function/forall
      [['A sort-l :implicit]
       ['subsingleton
        (function/app (function/const* 'type/subsingleton [L]) 'A)
        :implicit]]
      target)
     :value
     (function/lam
      [['A sort-l :implicit]
       ['subsingleton
        (function/app (function/const* 'type/subsingleton [L]) 'A)
        :implicit]]
      (function/app
       (function/const* 'logic/classical-cases []) nonempty-a target
       (function/lam
        [['inhabited nonempty-a]]
        (function/app
         'inhabited target
         (function/lam
          [['selected 'A]]
          (let [singleton
                (function/app (function/const* 'data/cons [L])
                              'A 'selected nil-a)]
            (witness
             L list-a cover singleton
             (function/lam
              [['value 'A]]
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (equality L 'A 'value 'selected)
               (finite-type/membership L 'A nil-a 'value)
               (function/app 'subsingleton 'value 'selected))))))))
       (function/lam
        [['not-inhabited (proposition/negation nonempty-a)]]
        (witness
         L list-a cover nil-a
         (function/lam
          [['value 'A]]
          (function/app
           (function/const* 'proposition/explode [])
           (finite-type/membership L 'A nil-a 'value)
           (function/app
            'not-inhabited
            (function/app
             (function/const* 'proposition/nonempty-intro [L])
             'A 'value))))))))}))

(def subtype-extensional-spec
  (let [set-a (finite-set/set-of 'A)
        element (subtype 'A 'source)
        element-equality (equality data-level element 'left 'right)
        value-equality
        (equality data-level 'A
                  (subtype-value 'A 'source 'left)
                  (subtype-value 'A 'source 'right))
        outer-motive
        (function/lam
         [['left element]]
         (function/forall
          [['right element] ['same-value value-equality]]
          element-equality))]
    {:name 'subtype/extensional
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :implicit]
       ['left element :explicit] ['right element :explicit]
       ['same-value value-equality :explicit]]
      element-equality)
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :implicit]
       ['left element :explicit]]
      (function/app
       (function/const* 'data/Subtype.rec [data-level zero])
       'A 'source outer-motive
       (function/lam
        [['left-value 'A]
         ['left-property (function/app 'source 'left-value)]
         ['right element]]
        (let [left-element
              (subtype-intro 'A 'source 'left-value 'left-property)
              inner-motive
              (function/lam
               [['candidate element]]
               (function/forall
                [['same-value
                  (equality data-level 'A 'left-value
                            (subtype-value 'A 'source 'candidate))]]
                (equality data-level element left-element 'candidate)))]
          (function/app
           (function/const* 'data/Subtype.rec [data-level zero])
           'A 'source inner-motive
           (function/lam
            [['right-value 'A]
             ['right-property (function/app 'source 'right-value)]
             ['same-value
              (equality data-level 'A 'left-value 'right-value)]]
            (let [transported-family
                  (function/lam
                   [['candidate 'A]]
                   (function/forall
                    [['property (function/app 'source 'candidate)]]
                    (equality
                     data-level element left-element
                     (subtype-intro 'A 'source 'candidate 'property))))
                  at-left
                  (function/lam
                   [['property (function/app 'source 'left-value)]]
                   (function/app
                    (function/const* 'equality/congruent-function
                                     [zero data-level])
                    (function/app 'source 'left-value) element
                    (function/lam
                     [['proof (function/app 'source 'left-value)]]
                     (subtype-intro 'A 'source 'left-value 'proof))
                    'left-property 'property
                    (function/app
                     (function/const* 'logic/proof-irrelevance [])
                     (function/app 'source 'left-value)
                     'left-property 'property)))]
              (function/app
               (function/app
                (function/const* 'equality/substitution [data-level])
                'A 'left-value 'right-value 'same-value
                transported-family at-left)
               'right-property)))
           'right)))
       'left))}))

(def finite-subtype-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        element (subtype 'A 'source)
        universal-element (universal U element)
        mapping
        (function/lam
         [['value element]] (subtype-value 'A 'source 'value))
        source-finite (finite-set/finite 'A 'source)
        element-finite (finite-type/finite data-level element)
        universal-element-finite
        (function/app (function/const* 'set/finite [U])
                      element universal-element)
        mapped
        (function/app (function/const* 'set/image [U U])
                      element 'A mapping universal-element)
        maps
        (function/lam
         [['value element :implicit]
          ['universal-member (function/app universal-element 'value)
           :explicit]]
         (subtype-property 'A 'source 'value))
        injection
        (function/lam
         [['left element :implicit]
          ['left-member (function/app universal-element 'left) :explicit]
          ['right element :implicit]
          ['right-member (function/app universal-element 'right) :explicit]
          ['same-value
           (equality data-level 'A
                     (function/app mapping 'left)
                     (function/app mapping 'right))]]
         (function/app
          (function/const* 'subtype/extensional [U])
          'A 'source 'left 'right 'same-value))]
    {:name 'set/finite-subtype-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :explicit]]
      (proposition/equivalence source-finite element-finite))
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :explicit]]
      (proposition/introduce-equivalence
       source-finite element-finite
       (function/lam
        [['source-finite-evidence source-finite]]
        (function/app
         (function/const* 'type/finite-of-finite-universal [U])
         element
         (function/app
          (function/const* 'set/finite-of-injection-maps-to [U U])
          element 'A mapping universal-element 'source maps injection
          'source-finite-evidence)))
       (function/lam
        [['element-finite-evidence element-finite]]
        (let [universal-finite-evidence
              (proposition/backward-equivalence
               universal-element-finite element-finite
               (function/app
                (function/const* 'type/finite-universal-equivalence [U])
                element)
               'element-finite-evidence)
              mapped-finite
              (function/app
               (function/const* 'set/finite-image-preserved [U U])
               element 'A universal-element mapping
               universal-finite-evidence)
              inclusion
              (function/lam
               [['value 'A]
                ['source-member (function/app 'source 'value)]]
               (let [selected
                     (subtype-intro 'A 'source 'value 'source-member)
                     image-predicate
                     (function/lam
                      [['input element]]
                      (proposition/conjunction
                       (function/app universal-element 'input)
                       (equality data-level 'A
                                 (function/app mapping 'input) 'value)))]
                 (witness
                  data-level element image-predicate selected
                  (conjoin
                   (function/app universal-element selected)
                   (equality data-level 'A
                             (function/app mapping selected) 'value)
                   (function/const* 'proposition/trivial [])
                   (function/app
                    (function/const* 'equality/reflexive [data-level])
                    'A 'value)))))]
          (function/app
           (function/const* 'set/finite-subset-preserved [U])
           'A 'source mapped inclusion mapped-finite)))))}))

(def finite-subtype-equality-spec
  (let [set-a (finite-set/set-of 'A)
        element (subtype 'A 'source)
        source-finite (finite-set/finite 'A 'source)
        element-finite (finite-type/finite data-level element)]
    {:name 'set/finite-subtype-proposition-equality
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :explicit]]
      (equality proposition-level 'Prop source-finite element-finite))
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :explicit]]
      (function/app
       (function/const* 'logic/proposition-extensionality [])
       source-finite element-finite
       (function/app
        (function/const* 'set/finite-subtype-equivalence [U])
        'A 'source)))}))

(def theorem-specs
  [finite-of-subsingleton-spec subtype-extensional-spec
   finite-subtype-equivalence-spec finite-subtype-equality-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-subtype expression failed elaboration"
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
          {:origin :native :producer :finite-subtype-boundary}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-subtype theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (into [subsingleton-spec] theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.subtype))
(defn definition-ids [checked-environment]
  (sorted-map
   (:name subsingleton-spec)
   (environment/resolve-id checked-environment (:name subsingleton-spec))))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
