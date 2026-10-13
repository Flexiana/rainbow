(ns rainbow.math.sets.finset.data
  "Computational finite sets: duplicate-free enumerations paired with proof data.

  The older `finset/Finset` is deliberately extensional and therefore cannot
  eliminate its propositional cover into executable data.  This representation
  keeps the enumeration in Type, carries duplicate-freedom in Prop, and projects
  to the extensional representation without changing the kernel."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def proposition-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def list-nat
  (function/app (function/const* 'data/List [type-level]) nat))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- membership [level element enumeration value]
  (function/app (function/const* 'list/membership [level])
                element enumeration value))

(defn- no-duplicates [level element enumeration]
  (function/app (function/const* 'list/no-duplicates [level])
                element enumeration))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- exact-range [upper]
  (function/app (function/const* 'finset-data/range []) upper))

(defn- range-list [upper]
  (function/app (function/const* 'list/nat-range []) upper))

(defn- below [value upper]
  (function/app (function/const* 'nat/strict-below []) value upper))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- succ [value]
  (function/app successor value))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- transitive [carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                carrier left middle right first second))

(def list-no-duplicates-spec
  {:name 'list/no-duplicates
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u]]
    (function/arrow (list-of 'A) 'Prop))
   :value
   (function/lam
    [['A type-u] ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level proposition-level])
     'A
     (function/lam [['ignored (list-of 'A)]] 'Prop)
     (proposition/truth)
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-distinct 'Prop]]
      (proposition/conjunction
       (proposition/negation (membership U 'A 'tail 'head))
       'tail-distinct))
     'source))})

(def finset-data-type-spec
  {:name 'finset-data/Finset
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type (function/forall [['A type-u]] type-u)
   :value
   (function/lam
    [['A type-u]]
    (function/app
     (function/const* 'data/Subtype [data-level])
     (list-of 'A)
     (function/lam
      [['source (list-of 'A)]]
      (no-duplicates U 'A 'source))))})

(def enumeration-spec
  {:name 'finset-data/enumeration
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]]
    (list-of 'A))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]]
    (function/app
     (function/const* 'subtype/value [data-level])
     (list-of 'A)
     (function/lam
      [['candidate (list-of 'A)]]
      (no-duplicates U 'A 'candidate))
     'source))})

(def duplicate-free-spec
  {:name 'finset-data/duplicate-free
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]]
    (no-duplicates U 'A (enumeration 'A 'source)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]]
    (function/app
     (function/const* 'subtype/property [data-level])
     (list-of 'A)
     (function/lam
      [['candidate (list-of 'A)]]
      (no-duplicates U 'A 'candidate))
     'source))})

(def to-set-spec
  {:name 'finset-data/to-set
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]]
    (function/app (function/const* 'set/Set [U]) 'A))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)] ['value 'A]]
    (membership U 'A (enumeration 'A 'source) 'value))})

(def to-extensional-spec
  (let [set-a (function/app (function/const* 'set/Set [U]) 'A)
        source-set
        (function/app (function/const* 'finset-data/to-set [U])
                      'A 'source)
        finite-predicate
        (function/lam
         [['candidate set-a]]
         (function/app (function/const* 'set/finite [U])
                       'A 'candidate))
        cover-predicate
        (function/lam
         [['candidate (list-of 'A)]]
         (function/forall
          [['value 'A] ['member (function/app source-set 'value)]]
          (membership U 'A 'candidate 'value)))
        cover
        (witness
         data-level (list-of 'A) cover-predicate
         (enumeration 'A 'source)
         (function/lam
          [['value 'A] ['member (function/app source-set 'value)]]
          'member))]
    {:name 'finset-data/to-extensional
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]]
      (function/app (function/const* 'finset/Finset [U]) 'A))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]]
      (function/app
       (function/const* 'data/subtype [data-level])
       set-a finite-predicate source-set cover))}))

(def card-spec
  {:name 'finset-data/card
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]] nat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]]
    (function/app (function/const* 'list/length [data-level])
                  'A (enumeration 'A 'source)))})

(def nat-sum-spec
  {:name 'list/nat-sum
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow list-nat nat)
   :value
   (function/lam
    [['source list-nat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nat
     (function/lam [['ignored list-nat]] nat)
     zero
     (function/lam
      [['head nat] ['tail list-nat] ['tail-sum nat]]
      (add 'head 'tail-sum))
     'source))})

(def sum-nat-spec
  {:name 'finset-data/sum-nat
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/arrow
    (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
    nat)
   :value
   (function/lam
    [['source
      (function/app (function/const* 'finset-data/Finset [zero-level]) nat)]]
    (function/app
     (function/const* 'list/nat-sum [])
     (function/app
      (function/const* 'finset-data/enumeration [zero-level])
      nat 'source)))})

(def member-range-below-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (function/forall
          [['value nat]
           ['member (membership zero-level nat (range-list 'upper) 'value)]]
          (below 'value 'upper)))]
    {:name 'nat/member-range-below
     :universes []
     :type
     (function/forall
      [['upper nat] ['value nat]
       ['member (membership zero-level nat (range-list 'upper) 'value)]]
      (below 'value 'upper))
     :value
     (function/lam
      [['upper nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['value nat]
         ['impossible (membership zero-level nat (range-list zero) 'value)]]
        (function/app (function/const* 'proposition/explode [])
                      (below 'value zero) 'impossible))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['value nat]
         ['member
          (membership zero-level nat (range-list (succ 'previous)) 'value)]]
        (let [head-equality (nat-equality 'value 'previous)
              tail-membership
              (membership zero-level nat (range-list 'previous) 'value)
              target (below 'value (succ 'previous))]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           head-equality tail-membership target 'member
           (function/lam
            [['same head-equality]]
            (let [start (add (succ 'value) zero)
                  middle (succ 'value)
                  finish (succ 'previous)
                  zero-right
                  (function/app
                   (function/const* 'algebra/nat-add-zero-right [])
                   (succ 'value))
                  successor-same
                  (function/app
                   (function/const* 'equality/congruent-function
                                    [type-level type-level])
                   nat nat successor 'value 'previous 'same)]
              (witness
               type-level nat
               (function/lam
                [['extra nat]]
                (nat-equality (add (succ 'value) 'extra)
                              (succ 'previous)))
               zero
               (transitive nat start middle finish
                           zero-right successor-same))))
           (function/lam
            [['tail-member tail-membership]]
            (function/app
             (function/const* 'proposition/use-witness [type-level])
             nat
             (function/lam
              [['extra nat]]
              (nat-equality (add (succ 'value) 'extra) 'previous))
             target
             (function/app 'induction-hypothesis 'value 'tail-member)
             (function/lam
              [['extra nat]
               ['same (nat-equality (add (succ 'value) 'extra) 'previous)]]
              (let [start (add (succ 'value) (succ 'extra))
                    middle (succ (add (succ 'value) 'extra))
                    finish (succ 'previous)
                    add-successor
                    (function/app
                     (function/const* 'algebra/nat-add-successor-right [])
                     (succ 'value) 'extra)
                    successor-same
                    (function/app
                     (function/const* 'equality/congruent-function
                                      [type-level type-level])
                     nat nat successor
                     (add (succ 'value) 'extra) 'previous 'same)]
                (witness
                 type-level nat
                 (function/lam
                  [['next-extra nat]]
                  (nat-equality (add (succ 'value) 'next-extra)
                                (succ 'previous)))
                 (succ 'extra)
                 (transitive nat start middle finish
                             add-successor successor-same)))))))))
       'upper))}))

(def nat-range-no-duplicates-spec
  (let [motive
        (function/lam
         [['upper nat]]
         (no-duplicates zero-level nat (range-list 'upper)))]
    {:name 'list/nat-range-no-duplicates
     :universes []
     :type
     (function/forall
      [['upper nat]]
      (no-duplicates zero-level nat (range-list 'upper)))
     :value
     (function/lam
      [['upper nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/const* 'proposition/trivial [])
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (let [member
              (membership zero-level nat (range-list 'previous) 'previous)
              not-member
              (function/lam
               [['evidence member]]
               (function/app
                (function/const* 'nat/not-strictly-below-self [])
                'previous
                (function/app
                 (function/const* 'nat/member-range-below [])
                 'previous 'previous 'evidence)))]
          (function/app
           (function/const* 'proposition/conjoin [])
           (proposition/negation member)
           (no-duplicates zero-level nat (range-list 'previous))
           not-member 'induction-hypothesis)))
       'upper))}))

(def range-spec
  {:name 'finset-data/range
   :kind :definition
   :universes []
   :transparency :reducible
   :type
   (function/arrow nat
                   (function/app
                    (function/const* 'finset-data/Finset [zero-level]) nat))
   :value
   (function/lam
    [['upper nat]]
    (function/app
     (function/const* 'data/subtype [type-level])
     list-nat
     (function/lam
      [['source list-nat]]
      (no-duplicates zero-level nat 'source))
     (range-list 'upper)
     (function/app
      (function/const* 'list/nat-range-no-duplicates []) 'upper)))})

(def enumeration-sound-spec
  (let [member
        (membership U 'A (enumeration 'A 'source) 'value)]
    {:name 'finset-data/enumeration-sound
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['value 'A] ['member member]]
      (function/app
       (function/const* 'finset-data/to-set [U]) 'A 'source 'value))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['value 'A] ['member member]]
      'member)}))

(def enumeration-complete-spec
  (let [member
        (function/app
         (function/const* 'finset-data/to-set [U]) 'A 'source 'value)]
    {:name 'finset-data/enumeration-complete
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['value 'A] ['member member]]
      (membership U 'A (enumeration 'A 'source) 'value))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['value 'A] ['member member]]
      'member)}))

(def sum-nat-enumeration-spec
  (let [source-type
        (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
        left
        (function/app (function/const* 'finset-data/sum-nat []) 'source)
        right
        (function/app
         (function/const* 'list/nat-sum [])
         (function/app
          (function/const* 'finset-data/enumeration [zero-level])
          nat 'source))]
    {:name 'finset-data/sum-nat-enumeration
     :universes []
     :type
     (function/forall [['source source-type]] (nat-equality left right))
     :value
     (function/lam
      [['source source-type]]
      (function/app
       (function/const* 'equality/reflexive [type-level]) nat left))}))

(def card-range-spec
  (let [card-range
        (function/app
         (function/const* 'finset-data/card [zero-level])
         nat (exact-range 'upper))
        motive
        (function/lam
         [['upper nat]]
         (nat-equality
          (function/app
           (function/const* 'finset-data/card [zero-level])
           nat (exact-range 'upper))
          'upper))]
    {:name 'finset-data/card-range
     :universes []
     :type
     (function/forall [['upper nat]] (nat-equality card-range 'upper))
     :value
     (function/lam
      [['upper nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/app
        (function/const* 'equality/reflexive [type-level]) nat zero)
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (function/app
         (function/const* 'equality/congruent-function
                          [type-level type-level])
         nat nat successor
         (function/app
          (function/const* 'finset-data/card [zero-level])
          nat (exact-range 'previous))
         'previous 'induction-hypothesis))
       'upper))}))

(def definition-specs
  [list-no-duplicates-spec finset-data-type-spec enumeration-spec
   duplicate-free-spec to-set-spec to-extensional-spec card-spec nat-sum-spec
   sum-nat-spec range-spec])

(def theorem-specs
  [member-range-below-spec nat-range-no-duplicates-spec
   enumeration-sound-spec enumeration-complete-spec
   sum-nat-enumeration-spec card-range-spec])

(def constant-aliases
  {"Finset" 'finset-data/Finset
   "Finset.range" 'finset-data/range
   "Finset.card" 'finset-data/card})

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Computational Finset expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :computational-finite-set-data}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Computational Finset declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment [list-no-duplicates-spec finset-data-type-spec enumeration-spec duplicate-free-spec to-set-spec to-extensional-spec card-spec nat-sum-spec sum-nat-spec member-range-below-spec nat-range-no-duplicates-spec range-spec enumeration-sound-spec enumeration-complete-spec sum-nat-enumeration-spec card-range-spec]))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.sets.finset.data))
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
