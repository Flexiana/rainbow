(ns rainbow.math.finite.bellman-iterate-monotone
  "A post-fixed nnrat value function lies below every finite iterate of the
  Bellman optimality operator.  Native and axiom-free on the D63 checkpoint."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-monotone :as monotone]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- succ [value]
  (function/app successor value))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- backup-operator
  [state action states transition reward discount]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount))

(defn- optimality-step [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(defn- iterate-value
  [state action actions fallback backup steps initial]
  (function/app (function/const* 'value/nnrat-iterate [U V])
                state action actions fallback backup steps initial))

(def value-below-optimality-iterate-zero-spec
  (let [iterated
        (iterate-value 'S 'A 'actions 'fallback 'backup zero 'value)]
    {:name 'value/nnrat-value-below-optimality-iterate-zero
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['state 'S]]
      (at-most (function/app 'value 'state)
               (function/app iterated 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['state 'S]]
      (let [value-at (function/app 'value 'state)
            zero-at (function/app iterated 'state)
            zero-unfold
            (function/app
             (function/const* 'value/nnrat-iterate-zero [U V])
             'S 'A 'actions 'fallback 'backup 'value 'state)
            value-equals-zero
            (function/app
             (function/const* 'equality/symmetric [type-level])
             nnrat zero-at value-at zero-unfold)]
        (function/app
         (function/const* 'equality/substitution [type-level])
         nnrat value-at zero-at value-equals-zero
         (function/lam [['upper nnrat]] (at-most value-at 'upper))
         (function/app
          (function/const* 'nnrat/at-most-reflexive []) value-at))))}))

(def value-below-optimality-iterate-successor-spec
  (let [previous-value
        (iterate-value 'S 'A 'actions 'fallback 'backup 'previous 'value)
        next-value
        (iterate-value 'S 'A 'actions 'fallback 'backup
                       (succ 'previous) 'value)
        step-at
        (fn [candidate state]
          (optimality-step 'S 'A 'actions 'fallback 'backup candidate state))
        successor-result
        (function/lam
         [['selected-state 'S]]
         (step-at previous-value 'selected-state))]
    {:name 'value/nnrat-value-below-optimality-iterate-successor
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['previous nat]
       ['below-successor
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at previous-value 'state)))]
       ['state 'S]]
      (at-most (function/app 'value 'state)
               (function/app next-value 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['previous nat]
       ['below-successor
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at previous-value 'state)))]
       ['state 'S]]
      (let [value-function (function/arrow 'S nnrat)
            lower-at (function/app 'value 'state)
            upper-step (step-at previous-value 'state)
            successor-unfold
            (function/app
             (function/const* 'value/nnrat-iterate-successor [U V])
             'S 'A 'actions 'fallback 'backup 'previous 'value)
            step-equals-next
            (function/app
             (function/const* 'equality/symmetric [data-u])
             value-function next-value successor-result successor-unfold)]
        (function/app
         (function/const* 'equality/substitution [data-u])
         value-function successor-result next-value step-equals-next
         (function/lam
          [['upper-value value-function]]
          (at-most lower-at (function/app 'upper-value 'state)))
         (function/app 'below-successor 'state))))}))

(def value-below-optimality-iterate-rec-spec
  (let [iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback 'backup steps 'value))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (at-most (function/app 'value 'state)
                   (function/app (iterated 'steps) 'state))))]
    {:name 'value/nnrat-value-below-optimality-iterate-rec
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['base (function/app motive zero)]
       ['successor-step
        (function/forall
         [['previous nat]
          ['induction-hypothesis (function/app motive 'previous)]]
         (function/app motive (succ 'previous)))]
       ['steps nat]
       ['state 'S]]
      (at-most (function/app 'value 'state)
               (function/app (iterated 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['base (function/app motive zero)]
       ['successor-step
        (function/forall
         [['previous nat]
          ['induction-hypothesis (function/app motive 'previous)]]
         (function/app motive (succ 'previous)))]
       ['steps nat]
       ['state 'S]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive 'base 'successor-step 'steps 'state))}))

(def value-below-optimality-iterate-generic-spec
  (let [iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback 'backup steps 'value))
        step-at
        (fn [candidate state]
          (optimality-step 'S 'A 'actions 'fallback 'backup candidate state))
        motive
        (function/lam
         [['steps nat]]
         (function/forall
          [['state 'S]]
          (at-most (function/app 'value 'state)
                   (function/app (iterated 'steps) 'state))))]
    {:name 'value/nnrat-value-below-optimality-iterate-generic
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at 'value 'state)))]
       ['step-monotone
        (function/forall
         [['lower-value (function/arrow 'S nnrat)]
          ['upper-value (function/arrow 'S nnrat)]
          ['pointwise
           (function/forall
            [['state 'S]]
            (at-most (function/app 'lower-value 'state)
                     (function/app 'upper-value 'state)))]
          ['state 'S]]
         (at-most (step-at 'lower-value 'state)
                  (step-at 'upper-value 'state)))]
       ['steps nat]
       ['state 'S]]
      (at-most (function/app 'value 'state)
               (function/app (iterated 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at 'value 'state)))]
       ['step-monotone
        (function/forall
         [['lower-value (function/arrow 'S nnrat)]
          ['upper-value (function/arrow 'S nnrat)]
          ['pointwise
           (function/forall
            [['state 'S]]
            (at-most (function/app 'lower-value 'state)
                     (function/app 'upper-value 'state)))]
          ['state 'S]]
         (at-most (step-at 'lower-value 'state)
                  (step-at 'upper-value 'state)))]
       ['steps nat]
       ['state 'S]]
      (function/app
       (function/const*
        'value/nnrat-value-below-optimality-iterate-rec [U V])
       'S 'A 'actions 'fallback 'backup 'value
       (function/lam
        [['current 'S]]
        (function/app
         (function/const*
          'value/nnrat-value-below-optimality-iterate-zero [U V])
         'S 'A 'actions 'fallback 'backup 'value 'current))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (let [previous-value (iterated 'previous)]
          (function/app
           (function/const*
            'value/nnrat-value-below-optimality-iterate-successor [U V])
           'S 'A 'actions 'fallback 'backup 'value 'previous
           (function/lam
            [['current 'S]]
            (let [lower-at (function/app 'value 'current)
                  lower-step (step-at 'value 'current)
                  upper-step (step-at previous-value 'current)]
              (function/app
               (function/const* 'nnrat/at-most-transitive [])
               lower-at lower-step upper-step
               (function/app 'below-step 'current)
               (function/app 'step-monotone 'value previous-value
                             'induction-hypothesis 'current)))))))
       'steps 'state))}))

(def value-below-optimality-iterate-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        iterated
        (fn [steps]
          (iterate-value 'S 'A 'actions 'fallback backup steps 'value))
        step-at
        (fn [candidate state]
          (optimality-step 'S 'A 'actions 'fallback backup candidate state))]
    {:name 'value/nnrat-value-below-optimality-iterate
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['value (function/arrow 'S nnrat)]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at 'value 'state)))]
       ['steps nat]
       ['state 'S]]
      (at-most (function/app 'value 'state)
               (function/app (iterated 'steps) 'state)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['actions (exact-finset-of V 'A)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['value (function/arrow 'S nnrat)]
       ['below-step
        (function/forall
         [['state 'S]]
         (at-most (function/app 'value 'state)
                  (step-at 'value 'state)))]
       ['steps nat]
       ['state 'S]]
      (function/app
       (function/const*
        'value/nnrat-value-below-optimality-iterate-generic [U V])
       'S 'A 'actions 'fallback backup 'value 'below-step
       (function/app
        (function/const* 'value/nnrat-optimality-step-monotone [U V])
        'S 'A 'states 'actions 'transition 'reward 'discount
        'fallback 'fallback-admissible)
       'steps 'state))}))

(def definition-specs [])
(def theorem-specs
  [value-below-optimality-iterate-zero-spec
   value-below-optimality-iterate-successor-spec
   value-below-optimality-iterate-rec-spec
   value-below-optimality-iterate-generic-spec
   value-below-optimality-iterate-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Finite Bellman iterate monotonicity expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-bellman-iterate-monotone}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Finite Bellman iterate monotonicity declaration rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.bellman-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman-iterate-monotone))
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
