(ns rainbow.algorithms.proofs.ahof.policy-iteration
  "AHoF D21 worked bounded policy-iteration step."
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
(def policy (function/arrow nat nat))
(def value-function (function/arrow nat nnrat))

(defn- finset-nat []
  (function/app (function/const* 'finset-data/Finset [zero-level]) nat))

(defn- member [source value]
  (function/app (function/const* 'finset-data/to-set [zero-level])
                nat source value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- improve [current score]
  (function/app
   (function/const* 'policy/nnrat-improve [zero-level zero-level])
   nat nat (function/const* 'ahof-d21/action-space []) current score))

(def state-space-spec
  {:name 'ahof-d21/state-space :kind :definition :universes []
   :type (finset-nat)
   :value (function/app (function/const* 'finset-data/range []) two)})

(def action-space-spec
  {:name 'ahof-d21/action-space :kind :definition :universes []
   :type (finset-nat)
   :value (function/app (function/const* 'finset-data/range []) two)})

(def current-policy-spec
  {:name 'ahof-d21/current-policy :kind :definition :universes []
   :type policy :value (function/lam [['ignored nat]] zero)})

(def evaluate-policy-spec
  {:name 'ahof-d21/evaluate-policy :kind :definition :universes []
   :type (function/arrow policy value-function)
   :value
   (function/lam
    [['ignored-policy policy]]
    (function/const* 'ahof-d20/worked-two-step-value []))})

(def action-score-spec
  {:name 'ahof-d21/action-score :kind :definition :universes []
   :type (function/arrow value-function nat nat nnrat)
   :value
   (function/lam
    [['value value-function] ['state nat] ['action nat]]
    (function/app
     (function/const* 'nnrat/make [])
     (function/app
      (function/const* 'algebra/nat-add []) 'action
      (function/app (function/const* 'nnrat/numerator [])
                    (function/app 'value 'state)))
     zero))})

(def improved-policy-spec
  {:name 'ahof-d21/improved-policy :kind :definition :universes []
   :type policy
   :value
   (improve
    (function/const* 'ahof-d21/current-policy [])
    (function/app
     (function/const* 'ahof-d21/action-score [])
     (function/app (function/const* 'ahof-d21/evaluate-policy [])
                   (function/const* 'ahof-d21/current-policy []))))})

(def iteration-step-spec
  {:name 'ahof-d21/iteration-step :kind :definition :universes []
   :type policy
   :value
   (function/app
    (function/const* 'policy/nnrat-iteration-step
                     [zero-level zero-level])
    nat nat (function/const* 'ahof-d21/action-space [])
    (function/const* 'ahof-d21/current-policy [])
    (function/const* 'ahof-d21/evaluate-policy [])
    (function/const* 'ahof-d21/action-score []))})

(def definition-specs
  [state-space-spec action-space-spec current-policy-spec
   evaluate-policy-spec action-score-spec improved-policy-spec
   iteration-step-spec])

(def current-admissible-spec
  {:name 'ahof-d21/current-policy-admissible
   :universes []
   :type
   (function/forall
    [['state nat]]
    (member (function/const* 'ahof-d21/action-space [])
            (function/app (function/const* 'ahof-d21/current-policy [])
                          'state)))
   :value
   (function/lam
    [['state nat]]
    (function/app
     (function/const* 'proposition/right-disjunct [])
     (equality nat zero one)
     (function/app
      (function/const* 'list/membership [zero-level])
      nat
      (function/app (function/const* 'data/cons [type-level])
                    nat zero
                    (function/app (function/const* 'data/nil [type-level]) nat))
      zero)
     (function/app
      (function/const* 'proposition/left-disjunct [])
      (equality nat zero zero)
      (function/app
       (function/const* 'list/membership [zero-level])
       nat (function/app (function/const* 'data/nil [type-level]) nat) zero)
      (function/app (function/const* 'equality/reflexive [type-level])
                    nat zero))))})

(def evaluation-phase-spec
  (let [evaluated
        (function/app (function/const* 'ahof-d21/evaluate-policy [])
                      (function/const* 'ahof-d21/current-policy []))]
    {:name 'ahof-d21/evaluation-phase
     :universes []
     :type (equality value-function evaluated evaluated)
     :value
     (function/app (function/const* 'equality/reflexive [type-level])
                   value-function evaluated)}))

(def improvement-phase-spec
  (let [actions (function/const* 'ahof-d21/action-space [])
        current (function/const* 'ahof-d21/current-policy [])
        score
        (function/app
         (function/const* 'ahof-d21/action-score [])
         (function/app (function/const* 'ahof-d21/evaluate-policy []) current))
        ;; Keep the generic improvement term visible in the certificate.  Going
        ;; through the worked definition alias makes conversion unfold the
        ;; complete two-step value function while checking both conjuncts and
        ;; can exhaust the ordinary kernel budget.
        improved (improve current score)
        admissible
        (function/forall [['state nat]]
                         (member actions (function/app improved 'state)))
        dominant
        (function/forall
         [['state nat] ['candidate nat]
          ['candidate-member (member actions 'candidate)]]
         (at-most (function/app score 'state 'candidate)
                  (function/app score 'state
                                (function/app improved 'state))))]
    {:name 'ahof-d21/improvement-phase
     :universes []
     :type (proposition/conjunction admissible dominant)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      admissible dominant
      (function/lam
       [['state nat]]
       (function/app
        (function/const* 'policy/nnrat-improve-is-admissible
                         [zero-level zero-level])
        nat nat actions current score
        (function/const* 'ahof-d21/current-policy-admissible []) 'state))
      (function/lam
       [['state nat] ['candidate nat]
        ['candidate-member (member actions 'candidate)]]
       (function/app
        (function/const* 'policy/nnrat-improve-dominates
                         [zero-level zero-level])
        nat nat actions current score 'state 'candidate
        'candidate-member)))}))

(def policy-iteration-step-spec
  (let [actions (function/const* 'ahof-d21/action-space [])
        current (function/const* 'ahof-d21/current-policy [])
        evaluate (function/const* 'ahof-d21/evaluate-policy [])
        action-score (function/const* 'ahof-d21/action-score [])
        score (function/app action-score (function/app evaluate current))
        step
        (function/app
         (function/const* 'policy/nnrat-iteration-step
                          [zero-level zero-level])
         nat nat actions current evaluate action-score)
        improved (improve current score)]
    {:name 'ahof-d21/policy-iteration-step
     :universes []
     :type
     (function/forall
      [['state nat]]
      (equality nat (function/app step 'state)
                (function/app improved 'state)))
     :value
     (function/app
      (function/const* 'policy/nnrat-iteration-step-unfold
                       [zero-level zero-level])
      nat nat actions current evaluate action-score)}))

(def theorem-specs
  [current-admissible-spec evaluation-phase-spec improvement-phase-spec
   policy-iteration-step-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF policy-iteration expression failed elaboration"
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
          {:origin :native :producer :ahof-d21-policy-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF policy-iteration declaration rejected"
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
