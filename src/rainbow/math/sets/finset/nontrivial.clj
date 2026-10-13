(ns rainbow.math.sets.finset.nontrivial
  "Nontrivial native Finsets through their extensional predicate view."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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

(defn- finset-of [carrier]
  (function/app (function/const* 'finset/Finset [U]) carrier))

(defn- finset-set [carrier source]
  (function/app (function/const* 'finset/to-set [U]) carrier source))

(defn- empty-finset [carrier]
  (function/app (function/const* 'finset/empty [U]) carrier))

(defn- singleton-finset [carrier value]
  (function/app (function/const* 'finset/singleton [U]) carrier value))

(defn- nontrivial [carrier source]
  (function/app (function/const* 'finset/nontrivial [U]) carrier source))

(defn- nonempty [carrier source]
  (function/app (function/const* 'finset/nonempty [U]) carrier source))

(defn- equality [carrier left right]
  (function/app (function/const* 'equality/Eq [data-level])
                carrier left right))

(defn- witness [carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [data-level])
                carrier predicate value evidence))

(defn- explode [target impossible]
  (function/app (function/const* 'proposition/explode [])
                target impossible))

(def nontrivial-spec
  {:name 'finset/nontrivial
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]] (function/arrow (finset-of 'A) 'Prop))
   :value
   (function/lam
    [['A type-u] ['source (finset-of 'A)]]
    (function/app (function/const* 'set/nontrivial [U])
                  'A (finset-set 'A 'source)))})

(def nontrivial-nonempty-spec
  (let [source-set (finset-set 'A 'source)
        left-predicate
        (function/lam
         [['left 'A]]
         (proposition/conjunction
          (function/app source-set 'left)
          (proposition/existence
           data-level 'A
           (function/lam
            [['right 'A]]
            (proposition/conjunction
             (function/app source-set 'right)
             (proposition/negation (equality 'A 'left 'right)))))))]
    {:name 'finset/nontrivial-nonempty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source (finset-of 'A) :implicit]
       ['evidence (nontrivial 'A 'source) :explicit]]
      (nonempty 'A 'source))
     :value
     (function/lam
      [['A type-u :implicit] ['source (finset-of 'A) :implicit]
       ['evidence (nontrivial 'A 'source) :explicit]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A left-predicate (nonempty 'A 'source) 'evidence
       (function/lam
        [['left 'A]
         ['both (function/app left-predicate 'left)]]
        (witness
         'A source-set 'left
         (function/app
          (function/const* 'proposition/left [])
          (function/app source-set 'left)
          (proposition/existence
           data-level 'A
           (function/lam
            [['right 'A]]
            (proposition/conjunction
             (function/app source-set 'right)
             (proposition/negation (equality 'A 'left 'right)))))
          'both)))))}))

(def empty-not-nontrivial-spec
  (let [source (empty-finset 'A)
        source-set (finset-set 'A source)
        left-predicate
        (function/lam
         [['left 'A]]
         (proposition/conjunction
          (function/app source-set 'left)
          (proposition/existence
           data-level 'A
           (function/lam
            [['right 'A]]
            (proposition/conjunction
             (function/app source-set 'right)
             (proposition/negation (equality 'A 'left 'right)))))))]
    {:name 'finset/empty-not-nontrivial
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (proposition/negation (nontrivial 'A source)))
     :value
     (function/lam
      [['A type-u :implicit] ['evidence (nontrivial 'A source)]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A left-predicate (proposition/falsity) 'evidence
       (function/lam
        [['left 'A] ['both (function/app left-predicate 'left)]]
        (function/app
         (function/const* 'proposition/left [])
         (function/app source-set 'left)
         (proposition/existence
          data-level 'A
          (function/lam
           [['right 'A]]
           (proposition/conjunction
            (function/app source-set 'right)
            (proposition/negation (equality 'A 'left 'right)))))
         'both))))}))

(def singleton-not-nontrivial-spec
  (let [source (singleton-finset 'A 'selected)
        source-set (finset-set 'A source)
        right-predicate
        (fn [left]
          (function/lam
           [['right 'A]]
           (proposition/conjunction
            (function/app source-set 'right)
            (proposition/negation (equality 'A left 'right)))))
        left-predicate
        (function/lam
         [['left 'A]]
         (proposition/conjunction
          (function/app source-set 'left)
          (proposition/existence data-level 'A (right-predicate 'left))))]
    {:name 'finset/singleton-not-nontrivial
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['selected 'A :implicit]]
      (proposition/negation (nontrivial 'A source)))
     :value
     (function/lam
      [['A type-u :implicit] ['selected 'A :implicit]
       ['evidence (nontrivial 'A source)]]
      (function/app
       (function/const* 'proposition/use-witness [data-level])
       'A left-predicate (proposition/falsity) 'evidence
       (function/lam
        [['left 'A] ['left-both (function/app left-predicate 'left)]]
        (let [left-member
              (function/app
               (function/const* 'proposition/left [])
               (function/app source-set 'left)
               (proposition/existence data-level 'A (right-predicate 'left))
               'left-both)
              right-exists
              (function/app
               (function/const* 'proposition/right [])
               (function/app source-set 'left)
               (proposition/existence data-level 'A (right-predicate 'left))
               'left-both)]
          (function/app
           (function/const* 'proposition/use-witness [data-level])
           'A (right-predicate 'left) (proposition/falsity) right-exists
           (function/lam
            [['right 'A]
             ['right-both (function/app (right-predicate 'left) 'right)]]
            (let [right-member
                  (function/app
                   (function/const* 'proposition/left [])
                   (function/app source-set 'right)
                   (proposition/negation (equality 'A 'left 'right))
                   'right-both)
                  different
                  (function/app
                   (function/const* 'proposition/right [])
                   (function/app source-set 'right)
                   (proposition/negation (equality 'A 'left 'right))
                   'right-both)
                  same
                  (function/app
                   (function/const* 'equality/transitive [data-level])
                   'A 'left 'selected 'right left-member
                   (function/app
                    (function/const* 'equality/symmetric [data-level])
                    'A 'right 'selected right-member))]
              (function/app different same))))))))}))

(def empty-nontrivial-proposition-equality-spec
  (let [left (nontrivial 'A (empty-finset 'A))
        right (proposition/falsity)]
    {:name 'finset/empty-nontrivial-proposition-equality
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
         [['evidence left]]
         (function/app
          (function/const* 'finset/empty-not-nontrivial [U])
          'A 'evidence))
        (function/lam
         [['impossible right]]
         (explode left 'impossible)))))}))

(def constant-aliases {"Finset.Nontrivial" 'finset/nontrivial})

(def definition-specs [nontrivial-spec])
(def theorem-specs
  [nontrivial-nonempty-spec empty-not-nontrivial-spec
   singleton-not-nontrivial-spec empty-nontrivial-proposition-equality-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finset-nontrivial expression failed elaboration"
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
          {:origin :native :producer :finset-set-nontrivial-bridge}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finset-nontrivial declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (into definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.finset.nontrivial))
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
