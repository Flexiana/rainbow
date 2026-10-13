(ns rainbow.algorithms.proofs.ahof.async-value-iteration
  "AHoF D23 worked asynchronous (Gauss-Seidel) value-iteration instance.

  Reuses the D22 worked finite MDP (two states, one action, zero reward, zero
  discount) so kernel normalization stays tractable, and adds a concrete
  single-state update schedule that always selects state 0 and preserves state
  1. This exhibits the pluggable state-selection strategy: the selected-state
  update law and the non-selected-state preservation law both hold at the
  worked model, the schedule-prefix recurrence unfolds, and a bounded
  asynchronous execution is exact."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def bool-false (function/const* 'data/false []))
(def value-function (function/arrow nat nnrat))

(defn- succ [value]
  (function/app successor value))

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

(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

;; Worked-model constants reused from the D22 checkpoint environment.
(def action-space (function/const* 'ahof-d22/action-space []))
(def fallback-action (function/const* 'ahof-d22/fallback-action []))
(def action-backup (function/const* 'ahof-d22/action-backup []))
(def initial-value (function/const* 'ahof-d22/initial-value []))

(defn- optimality [value state]
  (function/app
   (function/const* 'value/nnrat-optimality-step [zero-level zero-level])
   nat nat action-space fallback-action action-backup value state))

(defn- greedy [value state]
  (function/app
   (function/const* 'value/nnrat-greedy-action [zero-level zero-level])
   nat nat action-space fallback-action action-backup value state))

(defn- async-update
  ([choose value]
   (function/app
    (function/const* 'value/nnrat-async-update [zero-level zero-level])
    nat nat action-space fallback-action action-backup choose value))
  ([choose value state]
   (function/app
    (function/const* 'value/nnrat-async-update [zero-level zero-level])
    nat nat action-space fallback-action action-backup choose value state)))

(defn- async-iterate [schedule steps initial]
  (function/app
   (function/const* 'value/nnrat-async-iterate [zero-level zero-level])
   nat nat action-space fallback-action action-backup schedule steps initial))

(def schedule (function/const* 'ahof-d23/schedule []))

;; Definitions --------------------------------------------------------------

(def schedule-spec
  {:name 'ahof-d23/schedule :kind :definition :universes []
   :type (function/arrow nat nat bool)
   :value
   (function/lam
    [['ignored-step nat] ['state nat]]
    (decide-nat-equality 'state zero))})

(def async-sequence-spec
  {:name 'ahof-d23/async-sequence :kind :definition :universes []
   :type (function/arrow nat value-function)
   :value
   (function/lam
    [['steps nat]]
    (async-iterate schedule 'steps initial-value))})

(def one-step-async-spec
  {:name 'ahof-d23/one-step-async :kind :definition :universes []
   :type value-function
   :value (async-iterate schedule one initial-value)})

(def two-step-async-spec
  {:name 'ahof-d23/two-step-async :kind :definition :universes []
   :type value-function
   :value (async-iterate schedule two initial-value)})

(def definition-specs
  [schedule-spec async-sequence-spec one-step-async-spec two-step-async-spec])

;; Theorems -----------------------------------------------------------------

(def schedule-selects-zero-spec
  {:name 'ahof-d23/schedule-selects-zero :universes []
   :type
   (function/forall
    [['step nat]]
    (equality bool (function/app schedule 'step zero) bool-true))
   :value
   (function/lam
    [['step nat]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  bool bool-true))})

(def schedule-skips-one-spec
  {:name 'ahof-d23/schedule-skips-one :universes []
   :type
   (function/forall
    [['step nat]]
    (equality bool (function/app schedule 'step one) bool-false))
   :value
   (function/lam
    [['step nat]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  bool bool-false))})

(def selected-update-spec
  {:name 'ahof-d23/selected-update :universes []
   :type
   (function/forall
    [['step nat] ['value value-function]]
    (equality nnrat
              (async-update (function/app schedule 'step) 'value zero)
              (optimality 'value zero)))
   :value
   (function/lam
    [['step nat] ['value value-function]]
    (function/app
     (function/const* 'value/nnrat-async-update-selected
                      [zero-level zero-level])
     nat nat action-space fallback-action action-backup
     (function/app schedule 'step) 'value zero
     (function/app (function/const* 'ahof-d23/schedule-selects-zero [])
                   'step)))})

(def preserved-update-spec
  {:name 'ahof-d23/preserved-update :universes []
   :type
   (function/forall
    [['step nat] ['value value-function]]
    (equality nnrat
              (async-update (function/app schedule 'step) 'value one)
              (function/app 'value one)))
   :value
   (function/lam
    [['step nat] ['value value-function]]
    (function/app
     (function/const* 'value/nnrat-async-update-preserved
                      [zero-level zero-level])
     nat nat action-space fallback-action action-backup
     (function/app schedule 'step) 'value one
     (function/app (function/const* 'ahof-d23/schedule-skips-one [])
                   'step)))})

(def async-recurrence-spec
  (let [sequence (fn [steps] (async-iterate schedule steps initial-value))
        step
        (function/lam
         [['step-index nat] ['previous value-function]]
         (async-update (function/app schedule 'step-index) 'previous))
        base-law
        (function/forall
         [['state nat]]
         (equality nnrat (function/app (sequence zero) 'state)
                   (function/app initial-value 'state)))
        successor-law
        (function/forall
         [['steps nat]]
         (equality value-function (sequence (succ 'steps))
                   (function/app step 'steps (sequence 'steps))))]
    {:name 'ahof-d23/async-recurrence :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/lam
       [['state nat]]
       (function/app
        (function/const* 'value/nnrat-async-iterate-zero
                         [zero-level zero-level])
        nat nat action-space fallback-action action-backup
        schedule initial-value 'state))
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'value/nnrat-async-iterate-successor
                         [zero-level zero-level])
        nat nat action-space fallback-action action-backup
        schedule 'steps initial-value)))}))

(def greedy-actions-spec
  (let [value (function/const* 'ahof-d23/one-step-async [])
        selector (function/app schedule zero)
        admissible
        (function/forall
         [['state nat]]
         (member action-space (greedy value 'state)))
        dominant-at-zero
        (function/forall
         [['candidate nat] ['candidate-member (member action-space 'candidate)]]
         (at-most (function/app action-backup value zero 'candidate)
                  (async-update selector value zero)))]
    {:name 'ahof-d23/greedy-actions :universes []
     :type (proposition/conjunction admissible dominant-at-zero)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      admissible dominant-at-zero
      (function/lam
       [['state nat]]
       (function/app
        (function/const* 'value/nnrat-greedy-action-is-admissible
                         [zero-level zero-level])
        nat nat action-space fallback-action action-backup
        (function/const* 'ahof-d22/fallback-action-admissible [])
        value 'state))
      (function/lam
       [['candidate nat] ['candidate-member (member action-space 'candidate)]]
       (function/app
        (function/const* 'value/nnrat-async-update-selected-dominates
                         [zero-level zero-level])
        nat nat action-space fallback-action action-backup
        selector value zero
        (function/app (function/const* 'ahof-d23/schedule-selects-zero [])
                      zero)
        'candidate 'candidate-member)))}))

(def two-step-async-values-spec
  (let [worked (function/const* 'ahof-d23/two-step-async [])
        at-zero (equivalent (function/app worked zero) nnrat-zero)
        at-one (equivalent (function/app worked one) nnrat-zero)]
    {:name 'ahof-d23/two-step-async-values :universes []
     :type (proposition/conjunction at-zero at-one)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      at-zero at-one
      (reflexive-equivalence nnrat-zero)
      (reflexive-equivalence nnrat-zero))}))

(def async-value-iteration-spec
  (let [selected (:type selected-update-spec)
        preserved (:type preserved-update-spec)
        recurrence (:type async-recurrence-spec)
        results (:type two-step-async-values-spec)]
    {:name 'ahof-d23/async-value-iteration :universes []
     :type
     (proposition/conjunction
      selected
      (proposition/conjunction
       preserved (proposition/conjunction recurrence results)))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      selected
      (proposition/conjunction
       preserved (proposition/conjunction recurrence results))
      (function/const* 'ahof-d23/selected-update [])
      (function/app
       (function/const* 'proposition/conjoin [])
       preserved (proposition/conjunction recurrence results)
       (function/const* 'ahof-d23/preserved-update [])
       (function/app
        (function/const* 'proposition/conjoin [])
        recurrence results
        (function/const* 'ahof-d23/async-recurrence [])
        (function/const* 'ahof-d23/two-step-async-values []))))}))

(def theorem-specs
  [schedule-selects-zero-spec schedule-skips-one-spec
   selected-update-spec preserved-update-spec async-recurrence-spec
   greedy-actions-spec two-step-async-values-spec
   async-value-iteration-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF async value-iteration expression failed elaboration"
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
          {:origin :native :producer :ahof-d23-async-value-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF async value-iteration declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.async-value-iteration))
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
