(ns rainbow.math.finite.type
  "Native finite and infinite carrier propositions as finite List covers."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def L [:param 'l])
(def sort-l [:sort L])
(def predicate-level [:max [:succ [:zero]] L])

(defn list-of [level carrier]
  (function/app (function/const* 'data/List [level]) carrier))

(defn membership [level carrier enumeration value]
  (function/app (function/const* 'list/sort-membership [level])
                carrier enumeration value))

(defn finite [level carrier]
  (function/app (function/const* 'type/finite [level]) carrier))

(defn infinite [level carrier]
  (function/app (function/const* 'type/infinite [level]) carrier))

(def sort-membership-spec
  (let [list-a (list-of L 'A)]
    {:name 'list/sort-membership
     :kind :definition
     :universes ['l]
     :type
     (function/forall
      [['A sort-l] ['source list-a] ['value 'A]] 'Prop)
     :value
     (function/lam
      [['A sort-l] ['source list-a]]
      (function/app
       (function/const* 'data/List.rec [L predicate-level])
       'A
       (function/lam
        [['ignored list-a]] (function/arrow 'A 'Prop))
       (function/lam [['value 'A]] (proposition/falsity))
       (function/lam
        [['head 'A] ['tail list-a]
         ['tail-membership (function/arrow 'A 'Prop)] ['value 'A]]
        (proposition/disjunction
         (function/equality L 'A 'value 'head)
         (function/app 'tail-membership 'value)))
       'source))}))

(def finite-spec
  (let [list-a (list-of L 'A)
        cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A]] (membership L 'A 'enumeration 'value)))]
    {:name 'type/finite
     :kind :definition
     :universes ['l]
     :type (function/forall [['A sort-l]] 'Prop)
     :value
     (function/lam
      [['A sort-l]]
      (proposition/existence L list-a cover))}))

(def infinite-spec
  {:name 'type/infinite
   :kind :definition
   :universes ['l]
   :type (function/forall [['A sort-l]] 'Prop)
   :value
   (function/lam
    [['A sort-l]]
    (proposition/negation (finite L 'A)))})

(def definition-specs [sort-membership-spec finite-spec infinite-spec])
(def constant-aliases
  {"Finite" 'type/finite
   "Infinite" 'type/infinite})

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def product-level [:max U V])
(def product-data-level [:succ product-level])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- list-membership [carrier enumeration value]
  (function/app (function/const* 'list/membership [U])
                carrier enumeration value))

(defn- universal [carrier]
  (function/app (function/const* 'set/universal [U]) carrier))

(defn- set-finite [carrier]
  (function/app (function/const* 'set/finite [U])
                carrier (universal carrier)))

(defn- type-cover [carrier enumeration]
  (function/forall
   [['value carrier]] (membership data-level carrier enumeration 'value)))

(defn- set-cover [carrier enumeration]
  (function/forall
   [['value carrier]
    ['universal-member (function/app (universal carrier) 'value)]]
   (list-membership carrier enumeration 'value)))

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

(defn- set-universal-at [level carrier]
  (function/app (function/const* 'set/universal [level]) carrier))

(defn- set-finite-at [level carrier source]
  (function/app (function/const* 'set/finite [level]) carrier source))

(defn- set-infinite-at [level carrier source]
  (function/app (function/const* 'set/infinite [level]) carrier source))

(defn- set-nonempty-at [level carrier source]
  (function/app (function/const* 'set/nonempty [level]) carrier source))

(defn- type-nonempty-at [sort-level carrier]
  (function/app (function/const* 'proposition/nonempty [sort-level]) carrier))

(defn- list-membership-at [level carrier enumeration value]
  (function/app (function/const* 'list/membership [level])
                carrier enumeration value))

(defn- set-finite-source-to-type-finite
  [level sort-level carrier source all-member evidence]
  (let [list-a (list-of sort-level carrier)
        source-cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value carrier] ['member (function/app source 'value)]]
          (list-membership-at level carrier 'enumeration 'value)))
        target-cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value carrier]]
          (membership sort-level carrier 'enumeration 'value)))
        target (finite sort-level carrier)]
    (function/app
     (function/const* 'proposition/use-witness [sort-level])
     list-a source-cover target evidence
     (function/lam
      [['enumeration list-a]
       ['cover-evidence (function/app source-cover 'enumeration)]]
      (witness
       sort-level list-a target-cover 'enumeration
       (function/lam
        [['value carrier]]
        (function/app 'cover-evidence 'value
                      (function/app all-member 'value))))))))

(defn- type-finite-to-set-finite-source
  [level sort-level carrier source evidence]
  (let [list-a (list-of sort-level carrier)
        source-cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value carrier] ['member (function/app source 'value)]]
          (list-membership-at level carrier 'enumeration 'value)))
        target (set-finite-at level carrier source)
        type-cover-value
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value carrier]]
          (membership sort-level carrier 'enumeration 'value)))]
    (function/app
     (function/const* 'proposition/use-witness [sort-level])
     list-a type-cover-value target evidence
     (function/lam
      [['enumeration list-a]
       ['cover-evidence (function/app type-cover-value 'enumeration)]]
      (witness
       sort-level list-a source-cover 'enumeration
       (function/lam
        [['value carrier] ['member (function/app source 'value)]]
        (function/app 'cover-evidence 'value)))))))

(defn- set-nonempty-universal-to-type-nonempty
  [level sort-level carrier evidence]
  (let [universal-set (set-universal-at level carrier)
        target (type-nonempty-at sort-level carrier)]
    (function/app
     (function/const* 'proposition/use-witness [sort-level])
     carrier universal-set target evidence
     (function/lam
      [['value carrier]
       ['universal-member (function/app universal-set 'value)]]
      (function/app (function/const* 'proposition/nonempty-intro [sort-level])
                    carrier 'value)))))

(defn- type-nonempty-to-set-nonempty-universal
  [level sort-level carrier evidence]
  (let [universal-set (set-universal-at level carrier)
        target (set-nonempty-at level carrier universal-set)]
    (function/app
     evidence target
     (function/lam
      [['value carrier]]
      (witness sort-level carrier universal-set 'value
               (function/const* 'proposition/trivial []))))))

(defn- set-finite-to-type-finite [carrier evidence]
  (let [list-a (list-of data-level carrier)
        source-cover (function/lam [['enumeration list-a]]
                                   (set-cover carrier 'enumeration))
        target-cover (function/lam [['enumeration list-a]]
                                   (type-cover carrier 'enumeration))]
    (function/app
     (function/const* 'proposition/use-witness [data-level])
     list-a source-cover (finite data-level carrier) evidence
     (function/lam
      [['enumeration list-a]
       ['cover-evidence (set-cover carrier 'enumeration)]]
      (witness
       data-level list-a target-cover 'enumeration
       (function/lam
        [['value carrier]]
        (function/app 'cover-evidence 'value
                      (function/const* 'proposition/trivial []))))))))

(defn- type-finite-to-set-finite [carrier evidence]
  (let [list-a (list-of data-level carrier)
        source-cover (function/lam [['enumeration list-a]]
                                   (type-cover carrier 'enumeration))
        target-cover (function/lam [['enumeration list-a]]
                                   (set-cover carrier 'enumeration))]
    (function/app
     (function/const* 'proposition/use-witness [data-level])
     list-a source-cover (set-finite carrier) evidence
     (function/lam
      [['enumeration list-a]
       ['cover-evidence (type-cover carrier 'enumeration)]]
      (witness
       data-level list-a target-cover 'enumeration
       (function/lam
        [['value carrier]
         ['universal-member (function/app (universal carrier) 'value)]]
        (function/app 'cover-evidence 'value)))))))

(def finite-universal-equivalence-spec
  (let [left (set-finite 'A)
        right (finite data-level 'A)]
    {:name 'type/finite-universal-equivalence
     :kind :theorem
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (proposition/equivalence left right))
     :value
     (function/lam
      [['A type-u :implicit]]
      (proposition/introduce-equivalence
       left right
       (function/lam [['evidence left]]
                     (set-finite-to-type-finite 'A 'evidence))
       (function/lam [['evidence right]]
                     (type-finite-to-set-finite 'A 'evidence))))}))

(def finite-of-finite-universal-spec
  {:name 'type/finite-of-finite-universal
   :kind :theorem
   :universes ['u]
   :type
   (function/forall
    [['A type-u :implicit]
     ['evidence (set-finite 'A) :explicit]]
    (finite data-level 'A))
   :value
   (function/lam
    [['A type-u :implicit]
     ['evidence (set-finite 'A) :explicit]]
    (set-finite-to-type-finite 'A 'evidence))})

(def infinite-universal-equivalence-spec
  (let [left (function/app (function/const* 'set/infinite [U])
                           'A (universal 'A))
        right (infinite data-level 'A)
        set-finite-a (set-finite 'A)
        type-finite-a (finite data-level 'A)]
    {:name 'type/infinite-universal-equivalence
     :kind :theorem
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (proposition/equivalence left right))
     :value
     (function/lam
      [['A type-u :implicit]]
      (proposition/introduce-equivalence
       left right
       (function/lam
        [['not-set-finite left] ['type-evidence type-finite-a]]
        (function/app 'not-set-finite
                      (type-finite-to-set-finite 'A 'type-evidence)))
       (function/lam
        [['not-type-finite right] ['set-evidence set-finite-a]]
        (function/app 'not-type-finite
                      (set-finite-to-type-finite 'A 'set-evidence)))))}))

(def finite-of-not-infinite-spec
  (let [finite-a (finite data-level 'A)
        infinite-a (infinite data-level 'A)
        not-infinite (proposition/negation infinite-a)]
    {:name 'type/finite-of-not-infinite
     :kind :theorem
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['double-negation not-infinite :explicit]]
      finite-a)
     :value
     (function/lam
      [['A type-u :implicit] ['double-negation not-infinite :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       finite-a finite-a
       (function/lam [['evidence finite-a]] 'evidence)
       (function/lam
        [['not-finite (proposition/negation finite-a)]]
        (function/app
         (function/const* 'proposition/explode []) finite-a
         (function/app 'double-negation 'not-finite)))))}))

(def infinite-product-equivalence-spec
  (let [universal-a (set-universal-at U 'A)
        universal-b (set-universal-at V 'B)
        product (finite-set/product-type 'A 'B)
        product-set
        (finite-set/product-set 'A 'B universal-a universal-b)
        set-product-infinite
        (set-infinite-at product-level product product-set)
        type-product-finite (finite product-data-level product)
        type-product-infinite (infinite product-data-level product)
        set-a-infinite (set-infinite-at U 'A universal-a)
        set-b-infinite (set-infinite-at V 'B universal-b)
        type-a-infinite (infinite data-level 'A)
        type-b-infinite (infinite target-data-level 'B)
        set-a-nonempty (set-nonempty-at U 'A universal-a)
        set-b-nonempty (set-nonempty-at V 'B universal-b)
        type-a-nonempty (type-nonempty-at data-level 'A)
        type-b-nonempty (type-nonempty-at target-data-level 'B)
        set-left-case
        (proposition/conjunction set-a-infinite set-b-nonempty)
        set-right-case
        (proposition/conjunction set-b-infinite set-a-nonempty)
        set-either (proposition/disjunction set-left-case set-right-case)
        type-left-case
        (proposition/conjunction type-a-infinite type-b-nonempty)
        type-right-case
        (proposition/conjunction type-a-nonempty type-b-infinite)
        type-either (proposition/disjunction type-left-case type-right-case)
        set-equivalence
        (function/app
         (function/const* 'set/infinite-product-equivalence [U V])
         'A 'B universal-a universal-b)
        a-infinite-equivalence
        (function/app
         (function/const* 'type/infinite-universal-equivalence [U]) 'A)
        b-infinite-equivalence
        (function/app
         (function/const* 'type/infinite-universal-equivalence [V]) 'B)
        every-product-member
        (function/lam
         [['pair product]]
         (conjoin
          (proposition/truth) (proposition/truth)
          (function/const* 'proposition/trivial [])
          (function/const* 'proposition/trivial [])))]
    {:name 'type/infinite-product-equivalence
     :kind :theorem
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]]
      (proposition/equivalence type-product-infinite type-either))
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]]
      (proposition/introduce-equivalence
       type-product-infinite type-either
       (function/lam
        [['product-infinite type-product-infinite]]
        (let [set-product-infinite-evidence
              (function/lam
               [['product-set-finite
                 (set-finite-at product-level product product-set)]]
               (function/app
                'product-infinite
                (set-finite-source-to-type-finite
                 product-level product-data-level product product-set
                 every-product-member 'product-set-finite)))
              set-result
              (proposition/forward-equivalence
               set-product-infinite set-either set-equivalence
               set-product-infinite-evidence)]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           set-left-case set-right-case type-either set-result
           (function/lam
            [['left-both set-left-case]]
            (function/app
             (function/const* 'proposition/left-disjunct [])
             type-left-case type-right-case
             (conjoin
              type-a-infinite type-b-nonempty
              (proposition/forward-equivalence
               set-a-infinite type-a-infinite a-infinite-equivalence
               (left set-a-infinite set-b-nonempty 'left-both))
              (set-nonempty-universal-to-type-nonempty
               V target-data-level 'B
               (right set-a-infinite set-b-nonempty 'left-both)))))
           (function/lam
            [['right-both set-right-case]]
            (function/app
             (function/const* 'proposition/right-disjunct [])
             type-left-case type-right-case
             (conjoin
              type-a-nonempty type-b-infinite
              (set-nonempty-universal-to-type-nonempty
               U data-level 'A
               (right set-b-infinite set-a-nonempty 'right-both))
              (proposition/forward-equivalence
               set-b-infinite type-b-infinite b-infinite-equivalence
               (left set-b-infinite set-a-nonempty 'right-both))))))))
       (function/lam
        [['either-evidence type-either]]
        (let [set-either-evidence
              (function/app
               (function/const* 'proposition/use-disjunction [])
               type-left-case type-right-case set-either 'either-evidence
               (function/lam
                [['left-both type-left-case]]
                (function/app
                 (function/const* 'proposition/left-disjunct [])
                 set-left-case set-right-case
                 (conjoin
                  set-a-infinite set-b-nonempty
                  (proposition/backward-equivalence
                   set-a-infinite type-a-infinite a-infinite-equivalence
                   (left type-a-infinite type-b-nonempty 'left-both))
                  (type-nonempty-to-set-nonempty-universal
                   V target-data-level 'B
                   (right type-a-infinite type-b-nonempty 'left-both)))))
               (function/lam
                [['right-both type-right-case]]
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 set-left-case set-right-case
                 (conjoin
                  set-b-infinite set-a-nonempty
                  (proposition/backward-equivalence
                   set-b-infinite type-b-infinite b-infinite-equivalence
                   (right type-a-nonempty type-b-infinite 'right-both))
                  (type-nonempty-to-set-nonempty-universal
                   U data-level 'A
                   (left type-a-nonempty type-b-infinite 'right-both))))))
              set-product-infinite-evidence
              (proposition/backward-equivalence
               set-product-infinite set-either set-equivalence
               set-either-evidence)]
          (function/lam
           [['product-finite type-product-finite]]
           (function/app
            set-product-infinite-evidence
            (type-finite-to-set-finite-source
             product-level product-data-level product product-set
             'product-finite)))))))}))

(def theorem-specs
  [finite-universal-equivalence-spec finite-of-finite-universal-spec
   infinite-universal-equivalence-spec finite-of-not-infinite-spec
   infinite-product-equivalence-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-type expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (:kind spec)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if (= :definition (:kind spec))
                                  :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-carrier-list-cover}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-type declaration was rejected"
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
  (module/install-module checked-environment 'rainbow.math.finite.type))
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
