(ns rainbow.algorithms.proofs.ahof.value-iteration
  "AHoF D22 worked finite exact-rational value-iteration instance."
  (:refer-clojure :exclude [denominator numerator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def two (function/app successor one))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def value-function (function/arrow nat nnrat))

(defn- succ [value]
  (function/app successor value))

(defn- finset-nat []
  (function/app (function/const* 'finset-data/Finset [zero-level]) nat))

(defn- member [source value]
  (function/app (function/const* 'finset-data/to-set [zero-level])
                nat source value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- reflexive-equivalence [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

(defn- if-data [carrier condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                carrier condition decision then-value else-value))

(defn- backup [value state action]
  (function/app (function/const* 'ahof-d22/action-backup [])
                value state action))

(defn- bellman-backup [value state action]
  (function/app
   (function/const* 'bellman/nnrat-action-backup
                    [zero-level zero-level])
   nat nat (function/const* 'ahof-d22/state-space [])
   (function/const* 'ahof-d22/transition [])
   (function/const* 'ahof-d22/reward []) nnrat-zero
   value state action))

(defn- greedy [value state]
  (function/app
   (function/const* 'value/nnrat-greedy-action
                    [zero-level zero-level])
   nat nat (function/const* 'ahof-d22/action-space [])
   (function/const* 'ahof-d22/fallback-action [])
   (function/const* 'ahof-d22/action-backup []) value state))

(defn- optimality [value state]
  (function/app
   (function/const* 'value/nnrat-optimality-step
                    [zero-level zero-level])
   nat nat (function/const* 'ahof-d22/action-space [])
   (function/const* 'ahof-d22/fallback-action [])
   (function/const* 'ahof-d22/action-backup []) value state))

(defn- iterate-value [steps initial]
  (function/app
   (function/const* 'value/nnrat-iterate [zero-level zero-level])
   nat nat (function/const* 'ahof-d22/action-space [])
   (function/const* 'ahof-d22/fallback-action [])
   (function/const* 'ahof-d22/action-backup []) steps initial))

(def state-space-spec
  {:name 'ahof-d22/state-space :kind :definition :universes []
   :type (finset-nat)
   :value (function/app (function/const* 'finset-data/range []) two)})

(def action-space-spec
  {:name 'ahof-d22/action-space :kind :definition :universes []
   :type (finset-nat)
   :value (function/app (function/const* 'finset-data/range []) one)})

(def fallback-action-spec
  {:name 'ahof-d22/fallback-action :kind :definition :universes []
   :type (function/arrow nat nat)
   :value (function/lam [['ignored-state nat]] zero)})

(def transition-spec
  {:name 'ahof-d22/transition :kind :definition :universes []
   :type (function/arrow nat nat nat nnrat)
   :value
   (function/lam
    [['ignored-state nat] ['action nat] ['next-state nat]]
    (if-data nnrat
             (nat-equality 'action 'next-state)
             (decide-nat-equality 'action 'next-state)
             nnrat-one nnrat-zero))})

(def reward-spec
  {:name 'ahof-d22/reward :kind :definition :universes []
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['ignored-state nat] ['ignored-action nat]]
    nnrat-zero)})

(def initial-value-spec
  {:name 'ahof-d22/initial-value :kind :definition :universes []
   :type value-function
   :value (function/lam [['ignored-state nat]] nnrat-zero)})

(def action-backup-spec
  {:name 'ahof-d22/action-backup :kind :definition :universes []
   :type (function/arrow value-function nat nat nnrat)
   :value
   (function/lam
    [['value value-function] ['state nat] ['action nat]]
    (function/app (function/const* 'ahof-d22/reward [])
                  'state 'action))})

(def optimality-step-spec
  {:name 'ahof-d22/optimality-step :kind :definition :universes []
   :type (function/arrow value-function value-function)
   :value
   (function/lam
    [['value value-function] ['state nat]]
    (optimality 'value 'state))})

(def value-sequence-spec
  {:name 'ahof-d22/value-sequence :kind :definition :universes []
   :type (function/arrow nat value-function)
   :value
   (function/lam
    [['steps nat]]
    (iterate-value 'steps (function/const* 'ahof-d22/initial-value [])))})

(def one-step-value-spec
  {:name 'ahof-d22/one-step-value :kind :definition :universes []
   :type value-function
   :value
   (iterate-value one (function/const* 'ahof-d22/initial-value []))})

(def two-step-value-definition-spec
  {:name 'ahof-d22/two-step-value-function :kind :definition :universes []
   :type value-function
   :value
   (iterate-value two (function/const* 'ahof-d22/initial-value []))})

(def definition-specs
  [state-space-spec action-space-spec fallback-action-spec transition-spec
   reward-spec initial-value-spec action-backup-spec optimality-step-spec
   value-sequence-spec one-step-value-spec two-step-value-definition-spec])

(def fallback-admissible-spec
  {:name 'ahof-d22/fallback-action-admissible
   :universes []
   :type
   (function/forall
    [['state nat]]
    (member (function/const* 'ahof-d22/action-space [])
            (function/app (function/const* 'ahof-d22/fallback-action [])
                          'state)))
   :value
   (function/lam
    [['state nat]]
    (function/app
     (function/const* 'proposition/left-disjunct [])
     (equality nat zero zero)
     (function/app
      (function/const* 'list/membership [zero-level])
      nat (function/app (function/const* 'data/nil [type-level]) nat) zero)
     (function/app (function/const* 'equality/reflexive [type-level])
                   nat zero)))})

(defn- row-total [state action]
  (function/app
   (function/const* 'list/nnrat-map-sum [zero-level])
   nat
   (function/app (function/const* 'ahof-d22/transition []) state action)
   (function/app
    (function/const* 'finset-data/enumeration [zero-level])
    nat (function/const* 'ahof-d22/state-space []))))

(def action-backup-correspondence-spec
  {:name 'ahof-d22/action-backup-correspondence
   :universes []
   :type
   (function/forall
    [['value value-function] ['state nat] ['action nat]]
    (equivalent (bellman-backup 'value 'state 'action)
                (backup 'value 'state 'action)))
   :value
   (function/lam
    [['value value-function] ['state nat] ['action nat]]
    (reflexive-equivalence (backup 'value 'state 'action)))})

(def normalized-transition-rows-spec
  (let [zero-row (fn [state] (equivalent (row-total state zero) nnrat-one))
        one-row (fn [state] (equivalent (row-total state one) nnrat-one))]
    {:name 'ahof-d22/normalized-transition-rows
     :universes []
     :type
     (function/forall
      [['state nat]]
      (proposition/conjunction (zero-row 'state) (one-row 'state)))
     :value
     (function/lam
      [['state nat]]
      (function/app
       (function/const* 'proposition/conjoin [])
       (zero-row 'state) (one-row 'state)
       (function/app (function/const* 'nnrat/equivalent-reflexive [])
                     nnrat-one)
       (function/app (function/const* 'nnrat/equivalent-reflexive [])
                     nnrat-one)))}))

(def finite-horizon-recurrence-spec
  (let [sequence
        (fn [steps]
          (iterate-value steps (function/const* 'ahof-d22/initial-value [])))
        initial (function/const* 'ahof-d22/initial-value [])
        step
        (function/lam
         [['ignored-step nat] ['previous value-function]]
         (function/lam
          [['state nat]]
          (optimality 'previous 'state)))
        base-law
        (function/forall
         [['state nat]]
         (equality nnrat (function/app (sequence zero) 'state)
                   (function/app initial 'state)))
        successor-law
        (function/forall
         [['steps nat]]
         (equality value-function (sequence (succ 'steps))
                   (function/app step 'steps (sequence 'steps))))]
    {:name 'ahof-d22/finite-horizon-recurrence
     :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/lam
       [['state nat]]
       (function/app
        (function/const* 'value/nnrat-iterate-zero
                         [zero-level zero-level])
        nat nat (function/const* 'ahof-d22/action-space [])
        (function/const* 'ahof-d22/fallback-action [])
        (function/const* 'ahof-d22/action-backup []) initial 'state))
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'value/nnrat-iterate-successor
                         [zero-level zero-level])
        nat nat (function/const* 'ahof-d22/action-space [])
        (function/const* 'ahof-d22/fallback-action [])
        (function/const* 'ahof-d22/action-backup []) 'steps initial)))}))

(def greedy-actions-spec
  (let [actions (function/const* 'ahof-d22/action-space [])
        fallback (function/const* 'ahof-d22/fallback-action [])
        backup-function (function/const* 'ahof-d22/action-backup [])
        value (function/const* 'ahof-d22/one-step-value [])
        admissible
        (function/forall
         [['state nat]]
         (member actions (greedy value 'state)))
        dominant
        (function/forall
         [['state nat] ['candidate nat]
          ['candidate-member (member actions 'candidate)]]
         (at-most (backup value 'state 'candidate)
                  (optimality value 'state)))]
    {:name 'ahof-d22/greedy-actions
     :universes []
     :type (proposition/conjunction admissible dominant)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      admissible dominant
      (function/lam
       [['state nat]]
       (function/app
        (function/const* 'value/nnrat-greedy-action-is-admissible
                         [zero-level zero-level])
        nat nat actions fallback backup-function
        (function/const* 'ahof-d22/fallback-action-admissible [])
        value 'state))
      (function/lam
       [['state nat] ['candidate nat]
        ['candidate-member (member actions 'candidate)]]
       (function/app
        (function/const* 'value/nnrat-optimality-step-dominates
                         [zero-level zero-level])
        nat nat actions fallback backup-function value
        'state 'candidate 'candidate-member)))}))

(def two-step-value-spec
  (let [worked (function/const* 'ahof-d22/two-step-value-function [])
        at-zero (equivalent (function/app worked zero) nnrat-zero)
        at-one (equivalent (function/app worked one) nnrat-zero)]
    {:name 'ahof-d22/two-step-value
     :universes []
     :type (proposition/conjunction at-zero at-one)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      at-zero at-one
      (reflexive-equivalence nnrat-zero)
      (reflexive-equivalence nnrat-zero))}))

(def value-iteration-spec
  (let [normalized (:type normalized-transition-rows-spec)
        recurrence (:type finite-horizon-recurrence-spec)
        greedy-laws (:type greedy-actions-spec)
        results (:type two-step-value-spec)]
    {:name 'ahof-d22/value-iteration
     :universes []
     :type
     (proposition/conjunction
      normalized
      (proposition/conjunction
       recurrence (proposition/conjunction greedy-laws results)))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      normalized
      (proposition/conjunction
       recurrence (proposition/conjunction greedy-laws results))
      (function/const* 'ahof-d22/normalized-transition-rows [])
      (function/app
       (function/const* 'proposition/conjoin [])
       recurrence (proposition/conjunction greedy-laws results)
       (function/const* 'ahof-d22/finite-horizon-recurrence [])
       (function/app
        (function/const* 'proposition/conjoin [])
        greedy-laws results
        (function/const* 'ahof-d22/greedy-actions [])
        (function/const* 'ahof-d22/two-step-value []))))}))

(def theorem-specs
  [fallback-admissible-spec action-backup-correspondence-spec
   normalized-transition-rows-spec
   finite-horizon-recurrence-spec greedy-actions-spec two-step-value-spec
   value-iteration-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF value-iteration expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :ahof-d22-value-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF value-iteration declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (concat definition-specs theorem-specs)))

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
