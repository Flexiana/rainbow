(ns rainbow.math.finite.value-iteration
  "Finite Bellman optimality and bounded value iteration over exact rationals."
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

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- expectation [level element source mass value]
  (function/app
   (function/const* 'probability/nnrat-expectation [level])
   element source mass value))

(defn- action-backup
  [state-level action-level state action states transition reward discount
   value current chosen]
  (function/app
   (function/const* 'bellman/nnrat-action-backup
                    [state-level action-level])
   state action states transition reward discount value current chosen))

(defn- greedy-action
  [state-level action-level state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-greedy-action
                    [state-level action-level])
   state action actions fallback backup value current))

(defn- optimality-step
  [state-level action-level state action actions fallback backup value current]
  (function/app
   (function/const* 'value/nnrat-optimality-step
                    [state-level action-level])
   state action actions fallback backup value current))

(defn- iterate-value
  [state-level action-level state action actions fallback backup steps initial]
  (function/app
   (function/const* 'value/nnrat-iterate [state-level action-level])
   state action actions fallback backup steps initial))

(def action-backup-spec
  {:name 'bellman/nnrat-action-backup
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat] ['value (function/arrow 'S nnrat)]]
    (function/arrow 'S 'A nnrat))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat] ['value (function/arrow 'S nnrat)]
     ['state 'S] ['action 'A]]
    (add
     (function/app 'reward 'state 'action)
     (multiply
      'discount
      (expectation U 'S 'states
                   (function/app 'transition 'state 'action)
                   'value))))})

(def greedy-action-spec
  {:name 'value/nnrat-greedy-action
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]]
    (function/arrow 'S 'A))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)] ['state 'S]]
    (function/app
     (function/const* 'decision/finite-nnrat-argmax [V])
     'A 'actions (function/app 'fallback 'state)
     (function/app 'backup 'value 'state)))})

(def optimality-step-spec
  {:name 'value/nnrat-optimality-step
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)]]
    (function/arrow 'S nnrat))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['value (function/arrow 'S nnrat)] ['state 'S]]
    (function/app
     'backup 'value 'state
     (greedy-action U V 'S 'A 'actions 'fallback 'backup 'value 'state)))})

(def value-iterate-spec
  {:name 'value/nnrat-iterate
   :kind :definition
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]]
    (function/arrow nat (function/arrow 'S nnrat)
                    (function/arrow 'S nnrat)))
   :value
   (function/lam
    [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
     ['fallback (function/arrow 'S 'A)]
     ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
     ['steps nat] ['initial (function/arrow 'S nnrat)]]
    (function/app
     (function/const* 'data/Nat.rec [data-u])
     (function/lam [['ignored nat]] (function/arrow 'S nnrat))
     'initial
     (function/lam
      [['ignored-step nat] ['previous (function/arrow 'S nnrat)]]
      (function/lam
       [['state 'S]]
       (optimality-step U V 'S 'A 'actions 'fallback 'backup
                        'previous 'state)))
     'steps))})

(def definition-specs
  [action-backup-spec greedy-action-spec optimality-step-spec
   value-iterate-spec])

(def action-backup-unfold-spec
  (let [left
        (action-backup U V 'S 'A 'states 'transition 'reward 'discount
                       'value 'state 'action)
        right
        (add
         (function/app 'reward 'state 'action)
         (multiply
          'discount
          (expectation U 'S 'states
                       (function/app 'transition 'state 'action) 'value)))]
    {:name 'bellman/nnrat-action-backup-unfold
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat] ['value (function/arrow 'S nnrat)]
       ['state 'S] ['action 'A]]
      (function/equality type-level nnrat left right))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat] ['value (function/arrow 'S nnrat)]
       ['state 'S] ['action 'A]]
      (function/app (function/const* 'equality/reflexive [type-level])
                    nnrat left))}))

(def greedy-action-admissible-spec
  (let [selected
        (greedy-action U V 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/nnrat-greedy-action-is-admissible
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['value (function/arrow 'S nnrat)] ['state 'S]]
      (source-membership V 'A 'actions selected))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['value (function/arrow 'S nnrat)] ['state 'S]]
      (function/app
       (function/const* 'decision/finite-nnrat-argmax-is-member [V])
       'A 'actions (function/app 'fallback 'state)
       (function/app 'backup 'value 'state)
       (function/app 'fallback-admissible 'state)))}))

(def optimality-dominates-spec
  (let [selected
        (greedy-action U V 'S 'A 'actions 'fallback 'backup 'value 'state)
        optimum
        (optimality-step U V 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/nnrat-optimality-step-dominates
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)] ['state 'S]
       ['candidate 'A]
       ['candidate-member (source-membership V 'A 'actions 'candidate)]]
      (at-most (function/app 'backup 'value 'state 'candidate) optimum))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)] ['state 'S]
       ['candidate 'A]
       ['candidate-member (source-membership V 'A 'actions 'candidate)]]
      (function/app
       (function/const* 'decision/finite-nnrat-argmax-dominates [V])
       'A 'actions (function/app 'fallback 'state)
       (function/app 'backup 'value 'state) 'candidate 'candidate-member))}))

(def optimality-step-unfold-spec
  (let [selected
        (greedy-action U V 'S 'A 'actions 'fallback 'backup 'value 'state)
        optimum
        (optimality-step U V 'S 'A 'actions 'fallback 'backup 'value 'state)]
    {:name 'value/nnrat-optimality-step-unfold
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)] ['state 'S]]
      (function/equality
       type-level nnrat optimum
       (function/app 'backup 'value 'state selected)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)] ['state 'S]]
      (function/app (function/const* 'equality/reflexive [type-level])
                    nnrat optimum))}))

(def iterate-zero-spec
  (let [iterated
        (iterate-value U V 'S 'A 'actions 'fallback 'backup zero 'initial)]
    {:name 'value/nnrat-iterate-zero
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['initial (function/arrow 'S nnrat)] ['state 'S]]
      (function/equality type-level nnrat
                         (function/app iterated 'state)
                         (function/app 'initial 'state)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['initial (function/arrow 'S nnrat)] ['state 'S]]
      (function/app (function/const* 'equality/reflexive [type-level])
                    nnrat (function/app 'initial 'state)))}))

(def iterate-successor-spec
  (let [value-function (function/arrow 'S nnrat)
        previous
        (iterate-value U V 'S 'A 'actions 'fallback 'backup 'steps 'initial)
        next
        (iterate-value U V 'S 'A 'actions 'fallback 'backup
                       (succ 'steps) 'initial)
        step
        (function/lam
         [['ignored-step nat] ['value value-function]]
         (function/lam
          [['state 'S]]
          (optimality-step U V 'S 'A 'actions 'fallback 'backup
                           'value 'state)))]
    {:name 'value/nnrat-iterate-successor
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['steps nat] ['initial value-function]]
      (function/equality data-u value-function next
                         (function/app step 'steps previous)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['steps nat] ['initial value-function]]
      (function/app
       (function/const* 'nat/recursor-successor-constant [U])
       value-function 'initial step 'steps))}))

(def optimality-state-transfer-spec
  (let [dominance
        (fn [state candidate]
          (at-most
           (function/app 'backup 'value state candidate)
           (optimality-step U V 'S 'A 'actions 'fallback 'backup
                            'value state)))]
    {:name 'value/nnrat-optimality-state-transfer
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['left-state 'S] ['right-state 'S]
       ['left-action 'A]
       ['left-member (source-membership V 'A 'actions 'left-action)]
       ['right-action 'A]
       ['right-member (source-membership V 'A 'actions 'right-action)]]
      (proposition/conjunction
       (dominance 'left-state 'left-action)
       (dominance 'right-state 'right-action)))
     :value
     (function/lam
      [['S type-u] ['A type-v] ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['value (function/arrow 'S nnrat)]
       ['left-state 'S] ['right-state 'S]
       ['left-action 'A]
       ['left-member (source-membership V 'A 'actions 'left-action)]
       ['right-action 'A]
       ['right-member (source-membership V 'A 'actions 'right-action)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       (dominance 'left-state 'left-action)
       (dominance 'right-state 'right-action)
       (function/app
        (function/const* 'value/nnrat-optimality-step-dominates [U V])
        'S 'A 'actions 'fallback 'backup 'value
        'left-state 'left-action 'left-member)
       (function/app
        (function/const* 'value/nnrat-optimality-step-dominates [U V])
        'S 'A 'actions 'fallback 'backup 'value
        'right-state 'right-action 'right-member)))}))

(def theorem-specs
  [action-backup-unfold-spec greedy-action-admissible-spec
   optimality-dominates-spec optimality-step-unfold-spec iterate-zero-spec
   iterate-successor-spec optimality-state-transfer-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite value-iteration expression failed elaboration"
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
          {:origin :native :producer :finite-value-iteration}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite value-iteration declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.finite.value-iteration))
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
