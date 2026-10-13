(ns rainbow.math.sets.finset.filter
  "Certified predicates and extensional filtering for native Finsets."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def data-level [:succ U])
(def sort-u [:sort U])
(def type-u [:sort data-level])
(def bool-type (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))

(defn- equality [level carrier left right]
  (function/app (function/const* 'equality/Eq [level])
                carrier left right))

(defn- finset-of [element]
  (function/app (function/const* 'finset/Finset [U]) element))

(defn- set-of [element]
  (function/app (function/const* 'set/Set [U]) element))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- to-set [element source]
  (function/app (function/const* 'finset/to-set [U]) element source))

(defn- finite [element source]
  (function/app (function/const* 'set/finite [U]) element source))

(defn- finite-evidence [element source]
  (function/app (function/const* 'finset/finite-evidence [U])
                element source))

(defn- membership [element enumeration value]
  (function/app (function/const* 'list/membership [U])
                element enumeration value))

(defn- decidable-predicate [element predicate]
  (function/app (function/const* 'decision/DecidablePred [data-level])
                element predicate))

(defn- filter-finset [element predicate decision source]
  (function/app (function/const* 'finset/filter [U])
                element predicate decision source))

(defn- empty-finset [element]
  (function/app (function/const* 'finset/empty [U]) element))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- explode [target impossible]
  (function/app (function/const* 'proposition/explode [])
                target impossible))

(def decidable-predicate-spec
  (let [classifier (function/arrow 'A bool-type)
        classifier-correct
        (function/lam
         [['candidate classifier]]
         (function/forall
          [['value 'A]]
          (proposition/equivalence
           (function/app 'predicate 'value)
           (equality [:succ [:zero]] bool-type
                     (function/app 'candidate 'value) bool-true))))]
    {:name 'decision/DecidablePred
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A sort-u] ['predicate (function/arrow 'A 'Prop)]]
      [:sort [:max [:max [:succ [:zero]] U] [:succ [:zero]]]])
     :value
     (function/lam
      [['A sort-u] ['predicate (function/arrow 'A 'Prop)]]
      (function/app
       (function/const* 'data/Subtype [[:max [:succ [:zero]] U]])
                    classifier classifier-correct))}))

(def filter-spec
  (let [finset-a (finset-of 'A)
        set-a (set-of 'A)
        list-a (list-of 'A)
        source-set (to-set 'A 'source)
        filtered-set
        (function/lam
         [['value 'A]]
         (proposition/conjunction
          (function/app source-set 'value)
          (function/app 'predicate 'value)))
        finset-predicate
        (function/lam [['candidate set-a]] (finite 'A 'candidate))
        source-cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A] ['member (function/app source-set 'value)]]
          (membership 'A 'enumeration 'value)))
        filtered-cover
        (function/lam
         [['enumeration list-a]]
         (function/forall
          [['value 'A] ['member (function/app filtered-set 'value)]]
          (membership 'A 'enumeration 'value)))
        filtered-finite
        (function/app
         (function/const* 'proposition/use-witness [data-level])
         list-a source-cover (finite 'A filtered-set)
         (finite-evidence 'A 'source)
         (function/lam
          [['enumeration list-a]
           ['cover-evidence (function/app source-cover 'enumeration)]]
          (witness
           data-level list-a filtered-cover 'enumeration
           (function/lam
            [['value 'A]
             ['member (function/app filtered-set 'value)]]
            (function/app
             'cover-evidence 'value
             (function/app
              (function/const* 'proposition/left [])
              (function/app source-set 'value)
              (function/app 'predicate 'value) 'member))))))]
    {:name 'finset/filter
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['decision (decidable-predicate 'A 'predicate)]
       ['source finset-a]]
      finset-a)
     :value
     (function/lam
      [['A type-u] ['predicate (function/arrow 'A 'Prop)]
       ['decision (decidable-predicate 'A 'predicate)]
       ['source finset-a]]
      (function/app
       (function/const* 'data/subtype [data-level])
       set-a finset-predicate filtered-set filtered-finite))}))

(def filter-false-spec
  (let [false-predicate
        (function/lam [['ignored 'A]] (proposition/falsity))
        filtered
        (filter-finset 'A false-predicate 'decision 'source)
        empty (empty-finset 'A)
        filtered-set (to-set 'A filtered)
        empty-set (to-set 'A empty)]
    {:name 'finset/filter-false
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['decision (decidable-predicate 'A false-predicate) :implicit]
       ['source (finset-of 'A) :explicit]]
      (equality data-level (finset-of 'A) filtered empty))
     :value
     (function/lam
      [['A type-u :implicit]
       ['decision (decidable-predicate 'A false-predicate) :implicit]
       ['source (finset-of 'A) :explicit]]
      (function/app
       (function/const* 'finset/extensional [U])
       'A filtered empty
       (function/lam
        [['value 'A]]
        (let [filtered-member (function/app filtered-set 'value)
              empty-member (function/app empty-set 'value)]
          (function/app
           (function/const* 'proposition/equivalence-intro [])
           filtered-member empty-member
           (function/lam
            [['member filtered-member]]
            (function/app
             (function/const* 'proposition/right [])
             (function/app (to-set 'A 'source) 'value)
             (proposition/falsity) 'member))
           (function/lam
            [['impossible empty-member]]
            (explode filtered-member 'impossible)))))))}))

(def definition-specs [decidable-predicate-spec filter-spec])
(def theorem-specs [filter-false-spec])

(def constant-aliases
  {"DecidablePred" 'decision/DecidablePred
   "Finset.filter" 'finset/filter})

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finset-filter expression failed elaboration"
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
          {:origin :native :producer :certified-extensional-filter}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finset-filter declaration was rejected"
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
  (module/install-module checked-environment 'rainbow.math.sets.finset.filter))
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
