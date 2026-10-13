(ns rainbow.math.sets.finset.powerset
  "Finite-set powersets derived from extensional Set and Finset proof data."
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

(defn- finite [element source]
  (finite-set/finite element source))

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

(defn- finite-evidence [element source]
  (function/app (function/const* 'finset/finite-evidence [U])
                element source))

(defn- empty-finset [element]
  (function/app (function/const* 'finset/empty [U]) element))

(defn- subset [element left right]
  (function/app (function/const* 'finset/subset [U])
                element left right))

(defn- nonempty [element source]
  (function/app (function/const* 'finset/nonempty [U])
                element source))

(defn- set-powerset [element source]
  (function/app (function/const* 'set/powerset [U]) element source))

(defn- powerset [element source]
  (function/app (function/const* 'finset/powerset [U]) element source))

(defn- witness [level carrier predicate value evidence]
  (function/app (function/const* 'proposition/witness [level])
                carrier predicate value evidence))

(defn- proposition-congruence [carrier mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [data-level one])
   carrier 'Prop mapping left right same))

(defn- proposition-forward [left right same evidence]
  (function/app (function/const* 'equality/proposition-forward [])
                left right same evidence))

(defn- proposition-backward [left right same evidence]
  (function/app (function/const* 'equality/proposition-backward [])
                left right same evidence))

(def powerset-spec
  (let [set-a (set-of 'A)
        finset-a (finset-of 'A)
        set-finset-a (set-of finset-a)
        source-set (to-set 'A 'source)
        candidates
        (function/lam
         [['candidate finset-a]]
         (subset 'A 'candidate 'source))
        target (set-powerset 'A source-set)
        mapping
        (function/lam
         [['candidate finset-a]]
         (to-set 'A 'candidate))
        maps
        (function/lam
         [['candidate finset-a :implicit]
          ['candidate-subset (function/app candidates 'candidate) :explicit]]
         'candidate-subset)
        injection
        (function/lam
         [['left finset-a :implicit]
          ['left-member (function/app candidates 'left) :explicit]
          ['right finset-a :implicit]
          ['right-member (function/app candidates 'right) :explicit]
          ['same-set
           (equality set-a
                     (function/app mapping 'left)
                     (function/app mapping 'right))]]
         (function/app
          (function/const* 'subtype/value-injective [U])
          set-a (finset-predicate 'A) 'left 'right 'same-set))
        finite-candidates
        (function/app
         (function/const* 'set/finite-of-injection-maps-to [U U])
         finset-a set-a mapping candidates target maps injection
         (function/app
          (function/const* 'set/finite-powerset [U])
          'A source-set (finite-evidence 'A 'source)))]
    {:name 'finset/powerset
     :kind :definition
     :universes ['u]
     :transparency :reducible
     :type
     (function/forall
      [['A type-u] ['source finset-a]]
      (finset-of finset-a))
     :value
     (function/lam
      [['A type-u] ['source finset-a]]
      (function/app
       (function/const* 'data/subtype [data-level])
       set-finset-a (finset-predicate finset-a)
       candidates finite-candidates))}))

(def member-powerset-equivalent-subset-spec
  (let [finset-a (finset-of 'A)
        member
        (function/app (to-set finset-a (powerset 'A 'source)) 'candidate)
        candidate-subset (subset 'A 'candidate 'source)]
    {:name 'finset/member-powerset-equivalent-subset
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['source finset-a :explicit] ['candidate finset-a :explicit]]
      (proposition/equivalence member candidate-subset))
     :value
     (function/lam
      [['A type-u :implicit]
       ['source finset-a :explicit] ['candidate finset-a :explicit]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       member candidate-subset
       (function/lam [['evidence member]] 'evidence)
       (function/lam [['evidence candidate-subset]] 'evidence)))}))

(def self-member-powerset-spec
  (let [finset-a (finset-of 'A)]
    {:name 'finset/self-member-powerset
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :explicit]]
      (function/app (to-set finset-a (powerset 'A 'source)) 'source))
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :explicit]]
      (function/app
       (function/const* 'finset/subset-reflexive-explicit [U])
       'A 'source))}))

(def powerset-monotone-spec
  (let [finset-a (finset-of 'A)
        powerset-left (powerset 'A 'left)
        powerset-right (powerset 'A 'right)]
    {:name 'finset/powerset-monotone
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]
       ['left finset-a :explicit] ['right finset-a :explicit]
       ['left-subset-right (subset 'A 'left 'right) :explicit]]
      (subset finset-a powerset-left powerset-right))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left finset-a :explicit] ['right finset-a :explicit]
       ['left-subset-right (subset 'A 'left 'right) :explicit]
       ['candidate finset-a]
       ['candidate-subset-left
        (function/app (to-set finset-a powerset-left) 'candidate)]]
      (function/lam
       [['value 'A]
        ['candidate-member (function/app (to-set 'A 'candidate) 'value)]]
       (function/app
        'left-subset-right 'value
        (function/app 'candidate-subset-left 'value 'candidate-member))))}))

(def powerset-nonempty-spec
  (let [finset-a (finset-of 'A)
        target (powerset 'A 'source)]
    {:name 'finset/powerset-nonempty
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit] ['source finset-a :explicit]]
      (nonempty finset-a target))
     :value
     (function/lam
      [['A type-u :implicit] ['source finset-a :explicit]]
      (witness
       data-level finset-a (to-set finset-a target)
       (empty-finset 'A)
       (function/app
        (function/const* 'finset/empty-subset [U])
        'A 'source)))}))

(def powerset-injective-spec
  (let [finset-a (finset-of 'A)
        finset-finset-a (finset-of finset-a)
        set-finset-a (set-of finset-a)
        mapping
        (function/lam
         [['source finset-a]]
         (powerset 'A 'source))]
    {:name 'finset/powerset-injective
     :universes ['u]
     :type
     (function/forall
      [['A type-u :implicit]]
      (function/injective data-level data-level
                          finset-a finset-finset-a mapping))
     :value
     (function/lam
      [['A type-u :implicit]
       ['left finset-a] ['right finset-a]
       ['same-powersets
        (equality finset-finset-a
                  (powerset 'A 'left) (powerset 'A 'right))]]
      (let [left-powerset (powerset 'A 'left)
            right-powerset (powerset 'A 'right)
            left-powerset-set (to-set finset-a left-powerset)
            right-powerset-set (to-set finset-a right-powerset)
            same-powerset-sets
            (function/app
             (function/const* 'equality/congruent-function
                              [data-level data-level])
             finset-finset-a set-finset-a
             (function/lam
              [['candidate finset-finset-a]]
              (to-set finset-a 'candidate))
             left-powerset right-powerset 'same-powersets)
            left-membership-same
            (proposition-congruence
             set-finset-a
             (function/lam
              [['source set-finset-a]]
              (function/app 'source 'left))
             left-powerset-set right-powerset-set same-powerset-sets)
            right-membership-same
            (proposition-congruence
             set-finset-a
             (function/lam
              [['source set-finset-a]]
              (function/app 'source 'right))
             left-powerset-set right-powerset-set same-powerset-sets)
            left-subset-right
            (proposition-forward
             (function/app left-powerset-set 'left)
             (function/app right-powerset-set 'left)
             left-membership-same
             (function/app
              (function/const* 'finset/self-member-powerset [U])
              'A 'left))
            right-subset-left
            (proposition-backward
             (function/app left-powerset-set 'right)
             (function/app right-powerset-set 'right)
             right-membership-same
             (function/app
              (function/const* 'finset/self-member-powerset [U])
              'A 'right))]
        (function/app
         (function/const* 'finset/extensional [U])
         'A 'left 'right
         (function/lam
          [['value 'A]]
          (let [left-member (function/app (to-set 'A 'left) 'value)
                right-member (function/app (to-set 'A 'right) 'value)]
            (function/app
             (function/const* 'proposition/equivalence-intro [])
             left-member right-member
             (function/lam
              [['member left-member]]
              (function/app left-subset-right 'value 'member))
             (function/lam
              [['member right-member]]
              (function/app right-subset-left 'value 'member))))))))}))

(def constant-aliases
  {"Finset.powerset" 'finset/powerset})

(def definition-specs [powerset-spec])
(def theorem-specs
  [member-powerset-equivalent-subset-spec
   self-member-powerset-spec
   powerset-monotone-spec
   powerset-nonempty-spec
   powerset-injective-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finset-powerset expression failed elaboration"
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
          {:origin :native :producer :extensional-finset-powerset}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finset-powerset declaration was rejected"
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
