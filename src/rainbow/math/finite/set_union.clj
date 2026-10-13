(ns rainbow.math.finite.set-union
  "Reusable finite/infinite union facts as native proof data."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U finite-set/U)
(def I [:param 'i])
(def J [:param 'j])
(def type-u finite-set/type-u)
(def sort-i [:sort I])
(def sort-j [:sort J])
(def data-level finite-set/data-level)

(defn indexed-union [element index-level index family]
  (function/app (function/const* 'set/indexed-union [U index-level])
                element index family))

(defn singleton [element selected]
  (function/app (function/const* 'set/singleton [U]) element selected))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- explode [target impossible]
  (function/app (function/const* 'proposition/explode [])
                target impossible))

(def infinite-indexed-union-spec
  (let [set-a (finite-set/set-of 'A)
        family-type (function/arrow 'Index set-a)
        selected (function/app 'family 'index)
        union (indexed-union 'A I 'Index 'family)
        selected-infinite (finite-set/infinite 'A selected)
        union-infinite (finite-set/infinite 'A union)
        inclusion
        (function/lam
         [['value 'A] ['member (function/app selected 'value)]]
         (witness
          I 'Index
          (function/lam
           [['candidate 'Index]]
           (function/app 'family 'candidate 'value))
          'index 'member))]
    {:name 'set/infinite-indexed-union-member
     :universes ['u 'i]
     :type
     (function/forall
      [['A type-u :implicit]
       ['Index sort-i :implicit]
       ['family family-type :implicit]
       ['index 'Index :explicit]
       ['infinite-evidence selected-infinite :explicit]]
      union-infinite)
     :value
     (function/lam
      [['A type-u :implicit]
       ['Index sort-i :implicit]
       ['family family-type :implicit]
       ['index 'Index :explicit]
       ['infinite-evidence selected-infinite :explicit]]
      (function/app
       (function/const* 'set/infinite-mono [U])
       'A selected union inclusion 'infinite-evidence))}))

(def infinite-indexed-union2-spec
  (let [set-a (finite-set/set-of 'A)
        second-type (function/forall [['index 'Index]] sort-j)
        family-type
        (function/forall
         [['index 'Index]
          ['second (function/app 'Second 'index)]]
         set-a)
        selected (function/app 'family 'index 'second)
        inner-family
        (fn [outer]
          (function/lam
           [['inner (function/app 'Second outer)]]
           (function/app 'family outer 'inner)))
        inner-union
        (fn [outer]
          (indexed-union 'A J (function/app 'Second outer)
                         (inner-family outer)))
        outer-family
        (function/lam [['outer 'Index]] (inner-union 'outer))
        union (indexed-union 'A I 'Index outer-family)
        selected-infinite (finite-set/infinite 'A selected)
        union-infinite (finite-set/infinite 'A union)
        inclusion
        (function/lam
         [['value 'A] ['member (function/app selected 'value)]]
         (witness
          I 'Index
          (function/lam
           [['outer 'Index]]
           (function/app (inner-union 'outer) 'value))
          'index
          (witness
           J (function/app 'Second 'index)
           (function/lam
            [['inner (function/app 'Second 'index)]]
            (function/app 'family 'index 'inner 'value))
           'second 'member)))]
    {:name 'set/infinite-indexed-union2-member
     :universes ['u 'i 'j]
     :type
     (function/forall
      [['A type-u :implicit]
       ['Index sort-i :implicit]
       ['Second second-type :implicit]
       ['family family-type :implicit]
       ['index 'Index :explicit]
       ['second (function/app 'Second 'index) :explicit]
       ['infinite-evidence selected-infinite :explicit]]
      union-infinite)
     :value
     (function/lam
      [['A type-u :implicit]
       ['Index sort-i :implicit]
       ['Second second-type :implicit]
       ['family family-type :implicit]
       ['index 'Index :explicit]
       ['second (function/app 'Second 'index) :explicit]
       ['infinite-evidence selected-infinite :explicit]]
      (function/app
       (function/const* 'set/infinite-mono [U])
       'A selected union inclusion 'infinite-evidence))}))

(def infinite-union-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        joined (finite-set/union 'A 'left 'right)
        left-finite (finite-set/finite 'A 'left)
        right-finite (finite-set/finite 'A 'right)
        joined-finite (finite-set/finite 'A joined)
        left-infinite (finite-set/infinite 'A 'left)
        right-infinite (finite-set/infinite 'A 'right)
        joined-infinite (finite-set/infinite 'A joined)
        either-infinite
        (proposition/disjunction left-infinite right-infinite)
        left-inclusion
        (function/lam
         [['value 'A] ['member (function/app 'left 'value)]]
         (function/app (function/const* 'proposition/left-disjunct [])
                       (function/app 'left 'value)
                       (function/app 'right 'value) 'member))
        right-inclusion
        (function/lam
         [['value 'A] ['member (function/app 'right 'value)]]
         (function/app (function/const* 'proposition/right-disjunct [])
                       (function/app 'left 'value)
                       (function/app 'right 'value) 'member))]
    {:name 'set/infinite-union-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left set-a :implicit] ['right set-a :implicit]]
      (proposition/equivalence joined-infinite either-infinite))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left set-a :implicit] ['right set-a :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       joined-infinite either-infinite
       (function/lam
        [['joined-infinite-evidence joined-infinite]]
        (function/app
         (function/const* 'logic/classical-cases [])
         left-finite either-infinite
         (function/lam
          [['left-finite-evidence left-finite]]
          (function/app
           (function/const* 'logic/classical-cases [])
           right-finite either-infinite
           (function/lam
            [['right-finite-evidence right-finite]]
            (explode
             either-infinite
             (function/app
              'joined-infinite-evidence
              (function/app
               (function/const* 'set/finite-union-preserved [U])
               'A 'left 'right
               'left-finite-evidence 'right-finite-evidence))))
           (function/lam
            [['not-right-finite (proposition/negation right-finite)]]
            (function/app
             (function/const* 'proposition/right-disjunct [])
             left-infinite right-infinite 'not-right-finite))))
         (function/lam
          [['not-left-finite (proposition/negation left-finite)]]
          (function/app
           (function/const* 'proposition/left-disjunct [])
           left-infinite right-infinite 'not-left-finite))))
       (function/lam
        [['either-infinite-evidence either-infinite]]
        (function/app
         (function/const* 'proposition/use-disjunction [])
         left-infinite right-infinite joined-infinite
         'either-infinite-evidence
         (function/lam
          [['left-infinite-evidence left-infinite]]
          (function/app
           (function/const* 'set/infinite-mono [U])
           'A 'left joined left-inclusion 'left-infinite-evidence))
         (function/lam
          [['right-infinite-evidence right-infinite]]
          (function/app
           (function/const* 'set/infinite-mono [U])
           'A 'right joined right-inclusion
           'right-infinite-evidence))))))}))

(def finite-singleton-equivalence-spec
  (let [list-a (finite-set/list-of 'A)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        enumeration (finite-set/cons-list 'A 'selected nil-a)
        source (singleton 'A 'selected)
        source-finite (finite-set/finite 'A source)
        truth (proposition/truth)
        cover-predicate
        (function/lam
         [['candidate list-a]]
         (finite-set/cover 'A source 'candidate))
        enumeration-cover
        (function/lam
         [['value 'A] ['member (function/app source 'value)]]
         (function/app
          (function/const* 'proposition/left-disjunct [])
          (finite-set/equality 'A 'value 'selected)
          (finite-set/membership 'A nil-a 'value)
          'member))
        finite-evidence
        (witness data-level list-a cover-predicate
                 enumeration enumeration-cover)]
    {:name 'set/finite-singleton-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['selected 'A :explicit]]
      (proposition/equivalence source-finite truth))
     :value
     (function/lam
      [['A type-u :implicit] ['selected 'A :explicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       source-finite truth
       (function/lam
        [['ignored source-finite]]
        (function/const* 'proposition/trivial []))
       (function/lam [['ignored truth]] finite-evidence)))}))

(def finite-singleton-equality-spec
  (let [source-finite
        (finite-set/finite 'A (singleton 'A 'selected))
        truth (proposition/truth)]
    {:name 'set/finite-singleton-proposition-equality
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['selected 'A :explicit]]
      (proposition/equality [:succ [:zero]] 'Prop source-finite truth))
     :value
     (function/lam
      [['A type-u :implicit] ['selected 'A :explicit]]
      (function/app
       (function/const* 'logic/proposition-extensionality [])
       source-finite truth
       (function/app
        (function/const* 'set/finite-singleton-equivalence [U])
        'A 'selected)))}))

(def theorem-specs
  [infinite-indexed-union-spec infinite-indexed-union2-spec
   infinite-union-equivalence-spec finite-singleton-equivalence-spec
   finite-singleton-equality-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-set union theorem failed elaboration"
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
          {:origin :native :producer :finite-set-union-algebra}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-set union theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (doseq [required ['set/infinite-mono 'set/finite-union-preserved 'logic/classical-cases 'logic/proposition-extensionality]] (when-not (environment/resolve-id checked-environment required) (throw (ex-info "Finite-set union dependency is unavailable" {:error/category :finite-set/union-dependency-missing :required required})))) (reduce add-theorem checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.set-union))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
