(ns rainbow.math.finite.set-boundary
  "Classical boundary facts for native finite and infinite sets.

  These proofs turn repeated finite/infinite dichotomy arguments into reusable
  Clojure data.  The module is separate from both the constructive finite-set
  algebra and the finite-map transport layer so their historical proof and
  axiom profiles remain stable."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U finite-set/U)
(def data-level finite-set/data-level)
(def type-u finite-set/type-u)

(defn subsingleton [element source]
  (function/app (function/const* 'set/subsingleton [U]) element source))

(defn nontrivial [element source]
  (function/app (function/const* 'set/nontrivial [U]) element source))

(defn- left-disjunct [left right evidence]
  (function/app (function/const* 'proposition/left-disjunct [])
                left right evidence))

(defn- right-disjunct [left right evidence]
  (function/app (function/const* 'proposition/right-disjunct [])
                left right evidence))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- explode [target impossible]
  (function/app (function/const* 'proposition/explode [])
                target impossible))

(def finite-or-infinite-spec
  (let [set-a (finite-set/set-of 'A)
        source-finite (finite-set/finite 'A 'source)
        source-infinite (finite-set/infinite 'A 'source)
        target (proposition/disjunction source-finite source-infinite)]
    {:name 'set/finite-or-infinite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       source-finite target
       (function/lam
        [['finite-evidence source-finite]]
        (left-disjunct source-finite source-infinite 'finite-evidence))
       (function/lam
        [['not-finite (proposition/negation source-finite)]]
        (right-disjunct source-finite source-infinite 'not-finite))))}))

(def infinite-or-finite-spec
  (let [set-a (finite-set/set-of 'A)
        source-finite (finite-set/finite 'A 'source)
        source-infinite (finite-set/infinite 'A 'source)
        target (proposition/disjunction source-infinite source-finite)]
    {:name 'set/infinite-or-finite
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :explicit]]
      target)
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       source-finite target
       (function/lam
        [['finite-evidence source-finite]]
        (right-disjunct source-infinite source-finite 'finite-evidence))
       (function/lam
        [['not-finite (proposition/negation source-finite)]]
        (left-disjunct source-infinite source-finite 'not-finite))))}))

(def not-infinite-equivalence-spec
  (let [set-a (finite-set/set-of 'A)
        source-finite (finite-set/finite 'A 'source)
        source-infinite (finite-set/infinite 'A 'source)
        not-infinite (proposition/negation source-infinite)]
    {:name 'set/not-infinite-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source set-a :implicit]]
      (proposition/equivalence not-infinite source-finite))
     :value
     (function/lam
      [['A type-u :implicit] ['source set-a :implicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       not-infinite source-finite
       (function/lam
        [['not-infinite-evidence not-infinite]]
        (function/app
         (function/const* 'logic/classical-double-negation-elimination [])
         source-finite 'not-infinite-evidence))
       (function/lam
        [['finite-evidence source-finite]
         ['infinite-evidence source-infinite]]
        (function/app 'infinite-evidence 'finite-evidence))))}))

(def infinite-nonempty-spec
  (let [set-a (finite-set/set-of 'A)
        list-a (finite-set/list-of 'A)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        source-finite (finite-set/finite 'A 'source)
        source-infinite (finite-set/infinite 'A 'source)
        source-nonempty (finite-set/nonempty 'A 'source)
        cover-predicate
        (function/lam
         [['enumeration list-a]]
         (finite-set/cover 'A 'source 'enumeration))]
    {:name 'set/infinite-nonempty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['infinite-evidence source-infinite :explicit]]
      source-nonempty)
     :value
     (function/lam
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['infinite-evidence source-infinite :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       source-nonempty source-nonempty
       (function/lam [['nonempty-evidence source-nonempty]]
                     'nonempty-evidence)
       (function/lam
        [['not-nonempty (proposition/negation source-nonempty)]]
        (let [nil-cover
              (function/lam
               [['value 'A] ['source-member (function/app 'source 'value)]]
               (explode
                (finite-set/membership 'A nil-a 'value)
                (function/app
                 'not-nonempty
                 (witness data-level 'A 'source 'value 'source-member))))
              finite-evidence
              (witness data-level list-a cover-predicate nil-a nil-cover)]
          (explode source-nonempty
                   (function/app 'infinite-evidence finite-evidence))))))}))

(def finite-of-subsingleton-spec
  (let [set-a (finite-set/set-of 'A)
        list-a (finite-set/list-of 'A)
        nil-a (function/app (function/const* 'data/nil [data-level]) 'A)
        source-finite (finite-set/finite 'A 'source)
        source-nonempty (finite-set/nonempty 'A 'source)
        source-subsingleton (subsingleton 'A 'source)
        cover-predicate
        (function/lam
         [['enumeration list-a]]
         (finite-set/cover 'A 'source 'enumeration))]
    {:name 'set/finite-of-subsingleton
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['subsingleton-evidence source-subsingleton :explicit]]
      source-finite)
     :value
     (function/lam
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['subsingleton-evidence source-subsingleton :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       source-nonempty source-finite
       (function/lam
        [['nonempty-evidence source-nonempty]]
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         'A 'source source-finite 'nonempty-evidence
         (function/lam
          [['selected 'A] ['selected-member (function/app 'source 'selected)]]
          (let [enumeration (finite-set/cons-list 'A 'selected nil-a)
                enumeration-cover
                (function/lam
                 [['value 'A]
                  ['source-member (function/app 'source 'value)]]
                 (left-disjunct
                  (finite-set/equality 'A 'value 'selected)
                  (finite-set/membership 'A nil-a 'value)
                  (function/app 'subsingleton-evidence
                                'value 'source-member
                                'selected 'selected-member)))]
            (witness data-level list-a cover-predicate
                     enumeration enumeration-cover)))))
       (function/lam
        [['not-nonempty (proposition/negation source-nonempty)]]
        (let [nil-cover
              (function/lam
               [['value 'A] ['source-member (function/app 'source 'value)]]
               (explode
                (finite-set/membership 'A nil-a 'value)
                (function/app
                 'not-nonempty
                 (witness data-level 'A 'source 'value 'source-member))))]
          (witness data-level list-a cover-predicate nil-a nil-cover)))))}))

(def infinite-nontrivial-spec
  (let [set-a (finite-set/set-of 'A)
        source-finite (finite-set/finite 'A 'source)
        source-infinite (finite-set/infinite 'A 'source)
        source-subsingleton (subsingleton 'A 'source)
        source-nontrivial (nontrivial 'A 'source)]
    {:name 'set/infinite-nontrivial
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['infinite-evidence source-infinite :explicit]]
      source-nontrivial)
     :value
     (function/lam
      [['A type-u :implicit]
       ['source set-a :implicit]
       ['infinite-evidence source-infinite :explicit]]
      (function/app
       (function/const* 'logic/classical-cases [])
       source-nontrivial source-nontrivial
       (function/lam [['nontrivial-evidence source-nontrivial]]
                     'nontrivial-evidence)
       (function/lam
        [['not-nontrivial (proposition/negation source-nontrivial)]]
        (let [subsingleton-evidence
              (function/lam
               [['left 'A :implicit]
                ['left-member (function/app 'source 'left)]
                ['right 'A :implicit]
                ['right-member (function/app 'source 'right)]]
               (let [same (finite-set/equality 'A 'left 'right)
                     right-predicate
                     (function/lam
                      [['candidate 'A]]
                      (proposition/conjunction
                       (function/app 'source 'candidate)
                       (proposition/negation
                        (finite-set/equality 'A 'left 'candidate))))
                     left-predicate
                     (function/lam
                      [['candidate 'A]]
                      (proposition/conjunction
                       (function/app 'source 'candidate)
                       (proposition/existence
                        data-level 'A
                        (function/lam
                         [['other 'A]]
                         (proposition/conjunction
                          (function/app 'source 'other)
                          (proposition/negation
                           (finite-set/equality
                            'A 'candidate 'other)))))))]
                 (function/app
                  (function/const*
                   'logic/classical-double-negation-elimination [])
                  same
                  (function/lam
                   [['not-same (proposition/negation same)]]
                   (function/app
                    'not-nontrivial
                    (witness
                     data-level 'A left-predicate 'left
                     (function/app
                      (function/const* 'proposition/conjoin [])
                      (function/app 'source 'left)
                      (proposition/existence data-level 'A right-predicate)
                      'left-member
                      (witness
                       data-level 'A right-predicate 'right
                       (function/app
                        (function/const* 'proposition/conjoin [])
                        (function/app 'source 'right)
                        (proposition/negation same)
                        'right-member 'not-same)))))))))
              finite-evidence
              (function/app
               (function/const* 'set/finite-of-subsingleton [U])
               'A 'source subsingleton-evidence)]
          (explode source-nontrivial
                   (function/app 'infinite-evidence finite-evidence))))))}))

(def theorem-specs
  [finite-or-infinite-spec infinite-or-finite-spec
   not-infinite-equivalence-spec infinite-nonempty-spec
   finite-of-subsingleton-spec infinite-nontrivial-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite-set boundary theorem failed elaboration"
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
          {:origin :native
           :producer :classical-finite-set-boundary
           :logical/profile :classical}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite-set boundary theorem was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (when-not (and (environment/resolve-id checked-environment 'logic/classical-cases) (environment/resolve-id checked-environment 'logic/excluded-middle)) (throw (ex-info "Finite-set boundary proofs require classical activation" {:error/category :finite-set/classical-profile-required}))) (reduce add-theorem checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.set-boundary))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
