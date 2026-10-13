(ns rainbow.math.finite.async-value-iteration
  "Asynchronous (Gauss-Seidel) finite Bellman value iteration.

  The Bellman optimality operator is exactly the one proved for D22 finite
  value iteration; the only new content is a pluggable state-selection
  strategy. A `choose?` predicate delegates, per state, whether this stroke
  applies the optimality backup (selected states) or preserves the previous
  value (non-selected states). Bounded asynchronous iteration folds a schedule
  of such selectors over Nat recursion, so the selection order is a first-class
  strategy rather than a fixed synchronous sweep."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def type-v [:sort [:succ V]])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def bool-false (function/const* 'data/false []))

(defn- succ [value]
  (function/app successor value))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- if-data [carrier condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                carrier condition decision then-value else-value))

(defn- optimality-step
  [state-level action-level state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-optimality-step
                    [state-level action-level])
   state action actions fallback backup value current))

;; Shared surface fragments -------------------------------------------------

(def value-function (function/arrow 'S nnrat))
(def backup-type (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat))

(def context-binders
  [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
   ['fallback (function/arrow 'S 'A)]
   ['backup backup-type]])

(defn- opt [value state]
  (optimality-step U V 'S 'A 'actions 'fallback 'backup value state))

(defn- selected-condition [choose state]
  (equality bool (function/app choose state) bool-true))

(defn- async-update-body [choose value state]
  (if-data nnrat
           (selected-condition choose state)
           (function/app choose state)
           (opt value state)
           (function/app value state)))

(defn- async-update
  ([choose value]
   (function/app
    (function/const* 'value/nnrat-async-update [U V])
    'S 'A 'actions 'fallback 'backup choose value))
  ([choose value state]
   (function/app
    (function/const* 'value/nnrat-async-update [U V])
    'S 'A 'actions 'fallback 'backup choose value state)))

(defn- async-iterate [schedule steps initial]
  (function/app
   (function/const* 'value/nnrat-async-iterate [U V])
   'S 'A 'actions 'fallback 'backup schedule steps initial))

;; Definitions --------------------------------------------------------------

(def async-update-spec
  {:name 'value/nnrat-async-update
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)])
    (function/arrow 'S nnrat))
   :value
   (function/lam
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)]
          ['state 'S])
    (async-update-body 'choose 'value 'state))})

(def async-iterate-spec
  {:name 'value/nnrat-async-iterate
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['schedule (function/arrow nat 'S bool)])
    (function/arrow nat (function/arrow 'S nnrat)
                    (function/arrow 'S nnrat)))
   :value
   (function/lam
    (conj context-binders
          ['schedule (function/arrow nat 'S bool)]
          ['steps nat] ['initial (function/arrow 'S nnrat)])
    (function/app
     (function/const* 'data/Nat.rec [data-u])
     (function/lam [['ignored nat]] (function/arrow 'S nnrat))
     'initial
     (function/lam
      [['step-index nat] ['previous (function/arrow 'S nnrat)]]
      (async-update (function/app 'schedule 'step-index) 'previous))
     'steps))})

(def definition-specs [async-update-spec async-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def async-update-selected-spec
  {:name 'value/nnrat-async-update-selected
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['selected (selected-condition 'choose 'state)])
    (equality nnrat (async-update 'choose 'value 'state)
              (opt 'value 'state)))
   :value
   (function/lam
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['selected (selected-condition 'choose 'state)])
    (function/app
     (function/const* 'equality/reverse-substitution [type-level])
     bool (function/app 'choose 'state) bool-true 'selected
     (function/lam
      [['decision bool]]
      (equality nnrat
                (if-data nnrat (selected-condition 'choose 'state)
                         'decision (opt 'value 'state)
                         (function/app 'value 'state))
                (opt 'value 'state)))
     (function/app (function/const* 'equality/reflexive [type-level])
                   nnrat (opt 'value 'state))))})

(def async-update-preserved-spec
  {:name 'value/nnrat-async-update-preserved
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['non-selected
           (equality bool (function/app 'choose 'state) bool-false)])
    (equality nnrat (async-update 'choose 'value 'state)
              (function/app 'value 'state)))
   :value
   (function/lam
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['non-selected
           (equality bool (function/app 'choose 'state) bool-false)])
    (function/app
     (function/const* 'equality/reverse-substitution [type-level])
     bool (function/app 'choose 'state) bool-false 'non-selected
     (function/lam
      [['decision bool]]
      (equality nnrat
                (if-data nnrat (selected-condition 'choose 'state)
                         'decision (opt 'value 'state)
                         (function/app 'value 'state))
                (function/app 'value 'state)))
     (function/app (function/const* 'equality/reflexive [type-level])
                   nnrat (function/app 'value 'state))))})

(def async-iterate-zero-spec
  {:name 'value/nnrat-async-iterate-zero
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['schedule (function/arrow nat 'S bool)]
          ['initial (function/arrow 'S nnrat)] ['state 'S])
    (equality nnrat
              (function/app (async-iterate 'schedule zero 'initial) 'state)
              (function/app 'initial 'state)))
   :value
   (function/lam
    (conj context-binders
          ['schedule (function/arrow nat 'S bool)]
          ['initial (function/arrow 'S nnrat)] ['state 'S])
    (function/app (function/const* 'equality/reflexive [type-level])
                  nnrat (function/app 'initial 'state)))})

(def async-iterate-successor-spec
  (let [step
        (function/lam
         [['step-index nat] ['previous (function/arrow 'S nnrat)]]
         (async-update (function/app 'schedule 'step-index) 'previous))
        previous (async-iterate 'schedule 'steps 'initial)
        next (async-iterate 'schedule (succ 'steps) 'initial)]
    {:name 'value/nnrat-async-iterate-successor
     :universes ['u 'v]
     :type
     (function/forall
      (conj context-binders
            ['schedule (function/arrow nat 'S bool)]
            ['steps nat] ['initial (function/arrow 'S nnrat)])
      (function/equality data-u (function/arrow 'S nnrat) next
                         (function/app step 'steps previous)))
     :value
     (function/lam
      (conj context-binders
            ['schedule (function/arrow nat 'S bool)]
            ['steps nat] ['initial (function/arrow 'S nnrat)])
      (function/app
       (function/const* 'nat/recursor-successor-constant [U])
       (function/arrow 'S nnrat) 'initial step 'steps))}))

(def async-update-selected-dominates-spec
  {:name 'value/nnrat-async-update-selected-dominates
   :universes ['u 'v]
   :type
   (function/forall
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['selected (selected-condition 'choose 'state)]
          ['candidate 'A]
          ['candidate-member (source-membership V 'A 'actions 'candidate)])
    (at-most (function/app 'backup 'value 'state 'candidate)
             (async-update 'choose 'value 'state)))
   :value
   (function/lam
    (conj context-binders
          ['choose (function/arrow 'S bool)]
          ['value (function/arrow 'S nnrat)] ['state 'S]
          ['selected (selected-condition 'choose 'state)]
          ['candidate 'A]
          ['candidate-member (source-membership V 'A 'actions 'candidate)])
    (function/app
     (function/const* 'equality/substitution [type-level])
     nnrat (opt 'value 'state) (async-update 'choose 'value 'state)
     (function/app
      (function/const* 'equality/symmetric [type-level])
      nnrat (async-update 'choose 'value 'state) (opt 'value 'state)
      (function/app
       (function/const* 'value/nnrat-async-update-selected [U V])
       'S 'A 'actions 'fallback 'backup 'choose 'value 'state 'selected))
     (function/lam
      [['dominated nnrat]]
      (at-most (function/app 'backup 'value 'state 'candidate) 'dominated))
     (function/app
      (function/const* 'value/nnrat-optimality-step-dominates [U V])
      'S 'A 'actions 'fallback 'backup 'value 'state
      'candidate 'candidate-member)))})

(def async-state-schedule-transfer-spec
  (let [law
        (fn [schedule state]
          (equality nnrat (async-update schedule 'value state)
                    (opt 'value state)))
        selected
        (fn [schedule state]
          (function/app
           (function/const* 'value/nnrat-async-update-selected [U V])
           'S 'A 'actions 'fallback 'backup schedule 'value state))]
    {:name 'value/nnrat-async-state-schedule-transfer
     :universes ['u 'v]
     :type
     (function/forall
      (conj context-binders
            ['value (function/arrow 'S nnrat)]
            ['left-schedule (function/arrow 'S bool)]
            ['right-schedule (function/arrow 'S bool)]
            ['left-state 'S] ['right-state 'S]
            ['left-selected (selected-condition 'left-schedule 'left-state)]
            ['right-selected
             (selected-condition 'right-schedule 'right-state)])
      (proposition/conjunction
       (law 'left-schedule 'left-state)
       (law 'right-schedule 'right-state)))
     :value
     (function/lam
      (conj context-binders
            ['value (function/arrow 'S nnrat)]
            ['left-schedule (function/arrow 'S bool)]
            ['right-schedule (function/arrow 'S bool)]
            ['left-state 'S] ['right-state 'S]
            ['left-selected (selected-condition 'left-schedule 'left-state)]
            ['right-selected
             (selected-condition 'right-schedule 'right-state)])
      (function/app
       (function/const* 'proposition/conjoin [])
       (law 'left-schedule 'left-state)
       (law 'right-schedule 'right-state)
       (function/app (selected 'left-schedule 'left-state) 'left-selected)
       (function/app (selected 'right-schedule 'right-state)
                     'right-selected)))}))

(def theorem-specs
  [async-update-selected-spec async-update-preserved-spec
   async-iterate-zero-spec async-iterate-successor-spec
   async-update-selected-dominates-spec async-state-schedule-transfer-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite async value-iteration expression failed elaboration"
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
          {:origin :native :producer :finite-async-value-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite async value-iteration declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.finite.async-value-iteration))
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
