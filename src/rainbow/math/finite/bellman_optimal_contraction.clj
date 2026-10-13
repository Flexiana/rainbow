(ns rainbow.math.finite.bellman-optimal-contraction
  "Finite-argmax nonexpansiveness for the NNRAT Bellman optimality layer.

  The existing finite sup metric is a Nat/numerator construction, whereas
  value/nnrat-optimality-step lives directly in NonnegativeRational.  This
  module therefore states the metric-free epsilon form of max
  nonexpansiveness:

    (forall a in actions, f a <= g a + epsilon)
      -> max f <= max g + epsilon.

  The two-sided theorem says that pointwise additive epsilon-closeness is
  preserved by finite argmax.  Its optimality-step specialization transports
  through value/nnrat-optimality-step-unfold, keeping the reducible argmax
  implementation opaque to the proof.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.value-iteration :as fvi]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
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
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- finite-argmax [element actions fallback score]
  (function/app (function/const* 'decision/finite-nnrat-argmax [V])
                element actions fallback score))

(defn- maximum-value [element actions fallback score]
  (function/app score (finite-argmax element actions fallback score)))

(defn- greedy-action [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-greedy-action [U V])
                state action actions fallback backup value current))

(defn- optimality-step [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nnrat left right same))

(defn- substitution [left right same motive proof]
  (function/app (function/const* 'equality/substitution [type-level])
                nnrat left right same motive proof))

(def finite-argmax-additive-upper-bound-spec
  (let [left-maximum (maximum-value 'A 'actions 'fallback 'left)
        right-maximum (maximum-value 'A 'actions 'fallback 'right)]
    {:name 'decision/finite-nnrat-argmax-additive-upper-bound
     :universes ['v]
     :type
     (function/forall
      [['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership V 'A 'actions 'fallback)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['epsilon nnrat]
       ['pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'left 'candidate)
                  (add (function/app 'right 'candidate) 'epsilon)))]]
      (at-most left-maximum (add right-maximum 'epsilon)))
     :value
     (function/lam
      [['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership V 'A 'actions 'fallback)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['epsilon nnrat]
       ['pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'left 'candidate)
                  (add (function/app 'right 'candidate) 'epsilon)))]]
      (let [left-selected (finite-argmax 'A 'actions 'fallback 'left)
            right-selected (finite-argmax 'A 'actions 'fallback 'right)
            left-selected-member
            (function/app
             (function/const* 'decision/finite-nnrat-argmax-is-member [V])
             'A 'actions 'fallback 'left 'fallback-member)
            selected-pointwise
            (function/app 'pointwise left-selected left-selected-member)
            right-dominates
            (function/app
             (function/const* 'decision/finite-nnrat-argmax-dominates [V])
             'A 'actions 'fallback 'right
             left-selected left-selected-member)
            padded-dominance
            (function/app
             (function/const* 'nnrat/add-right-monotone [])
             'epsilon
             (function/app 'right left-selected)
             (function/app 'right right-selected)
             right-dominates)]
        (function/app
         (function/const* 'nnrat/at-most-transitive [])
         left-maximum
         (add (function/app 'right left-selected) 'epsilon)
         (add right-maximum 'epsilon)
         selected-pointwise padded-dominance)))}))

(def finite-argmax-additively-nonexpansive-spec
  (let [left-maximum (maximum-value 'A 'actions 'fallback 'left)
        right-maximum (maximum-value 'A 'actions 'fallback 'right)
        left-to-right
        (at-most left-maximum (add right-maximum 'epsilon))
        right-to-left
        (at-most right-maximum (add left-maximum 'epsilon))]
    {:name 'decision/finite-nnrat-argmax-additively-nonexpansive
     :universes ['v]
     :type
     (function/forall
      [['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership V 'A 'actions 'fallback)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'left 'candidate)
                  (add (function/app 'right 'candidate) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'right 'candidate)
                  (add (function/app 'left 'candidate) 'epsilon)))]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback 'A]
       ['fallback-member (source-membership V 'A 'actions 'fallback)]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'left 'candidate)
                  (add (function/app 'right 'candidate) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['candidate 'A]
          ['member (source-membership V 'A 'actions 'candidate)]]
         (at-most (function/app 'right 'candidate)
                  (add (function/app 'left 'candidate) 'epsilon)))]]
      (function/app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (function/app
        (function/const*
         'decision/finite-nnrat-argmax-additive-upper-bound [V])
        'A 'actions 'fallback 'fallback-member
        'left 'right 'epsilon 'left-pointwise)
       (function/app
        (function/const*
         'decision/finite-nnrat-argmax-additive-upper-bound [V])
        'A 'actions 'fallback 'fallback-member
        'right 'left 'epsilon 'right-pointwise)))}))

(def optimality-step-additive-upper-bound-spec
  (let [left-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'left-value 'state)
        right-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'right-value 'state)]
    {:name 'value/nnrat-optimality-step-additive-upper-bound
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['state 'S]
       ['pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'left-value 'state 'action)
                  (add (function/app 'backup 'right-value 'state 'action)
                       'epsilon)))]]
      (at-most left-step (add right-step 'epsilon)))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['state 'S]
       ['pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'left-value 'state 'action)
                  (add (function/app 'backup 'right-value 'state 'action)
                       'epsilon)))]]
      (let [left-score
            (function/lam
             [['action 'A]]
             (function/app 'backup 'left-value 'state 'action))
            right-score
            (function/lam
             [['action 'A]]
             (function/app 'backup 'right-value 'state 'action))
            fallback-action (function/app 'fallback 'state)
            left-selected
            (finite-argmax 'A 'actions fallback-action left-score)
            right-selected
            (finite-argmax 'A 'actions fallback-action right-score)
            left-selected-value (function/app left-score left-selected)
            right-selected-value (function/app right-score right-selected)
            maximum-bound
            (function/app
             (function/const*
              'decision/finite-nnrat-argmax-additive-upper-bound [V])
             'A 'actions fallback-action
             (function/app 'fallback-admissible 'state)
             left-score right-score 'epsilon 'pointwise)
            left-unfold
            (function/app
             (function/const* 'value/nnrat-optimality-step-unfold [U V])
             'S 'A 'actions 'fallback 'backup 'left-value 'state)
            right-unfold
            (function/app
             (function/const* 'value/nnrat-optimality-step-unfold [U V])
             'S 'A 'actions 'fallback 'backup 'right-value 'state)
            expose-left
            (substitution
             left-selected-value left-step
             (symmetric left-step left-selected-value left-unfold)
             (function/lam
              [['candidate nnrat]]
              (at-most 'candidate (add right-selected-value 'epsilon)))
             maximum-bound)]
        (substitution
         right-selected-value right-step
         (symmetric right-step right-selected-value right-unfold)
         (function/lam
          [['candidate nnrat]]
          (at-most left-step (add 'candidate 'epsilon)))
         expose-left)))}))

(def optimality-step-additively-nonexpansive-spec
  (let [left-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'left-value 'state)
        right-step
        (optimality-step 'S 'A 'actions 'fallback 'backup 'right-value 'state)
        left-to-right (at-most left-step (add right-step 'epsilon))
        right-to-left (at-most right-step (add left-step 'epsilon))]
    {:name 'value/nnrat-optimality-step-additively-nonexpansive
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['state 'S]
       ['left-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'left-value 'state 'action)
                  (add (function/app 'backup 'right-value 'state 'action)
                       'epsilon)))]
       ['right-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'right-value 'state 'action)
                  (add (function/app 'backup 'left-value 'state 'action)
                       'epsilon)))]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['actions (exact-finset-of V 'A)]
       ['fallback (function/arrow 'S 'A)]
       ['fallback-admissible
        (function/forall
         [['current 'S]]
         (source-membership V 'A 'actions
                            (function/app 'fallback 'current)))]
       ['backup (function/arrow (function/arrow 'S nnrat) 'S 'A nnrat)]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['state 'S]
       ['left-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'left-value 'state 'action)
                  (add (function/app 'backup 'right-value 'state 'action)
                       'epsilon)))]
       ['right-pointwise
        (function/forall
         [['action 'A]
          ['member (source-membership V 'A 'actions 'action)]]
         (at-most (function/app 'backup 'right-value 'state 'action)
                  (add (function/app 'backup 'left-value 'state 'action)
                       'epsilon)))]]
      (function/app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (function/app
        (function/const*
         'value/nnrat-optimality-step-additive-upper-bound [U V])
        'S 'A 'actions 'fallback 'fallback-admissible 'backup
        'left-value 'right-value 'epsilon 'state 'left-pointwise)
       (function/app
        (function/const*
         'value/nnrat-optimality-step-additive-upper-bound [U V])
        'S 'A 'actions 'fallback 'fallback-admissible 'backup
        'right-value 'left-value 'epsilon 'state 'right-pointwise)))}))

(def theorem-specs
  [finite-argmax-additive-upper-bound-spec
   finite-argmax-additively-nonexpansive-spec
   optimality-step-additive-upper-bound-spec
   optimality-step-additively-nonexpansive-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Finite Bellman optimal contraction expression failed elaboration"
                {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-bellman-optimal-contraction}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Finite Bellman optimal contraction theorem was rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (let [base (-> checked-environment fvi/extend-environment add-monotone/extend-environment)] (reduce add-spec base theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman-optimal-contraction))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
