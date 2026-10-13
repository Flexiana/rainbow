(ns rainbow.math.finite.bellman-backup-contraction
  "Discount-scaled contraction of finite NNRAT Bellman backups and T*.

  A normalized transition row transports two-sided additive epsilon-closeness
  of value functions to two-sided additive (discount*epsilon)-closeness of a
  fixed action backup.  With every transition row normalized, finite argmax
  nonexpansiveness lifts the same estimate to the Bellman optimality step.

  The optimality proof treats value/nnrat-optimality-step as opaque: all
  argmax reasoning stays behind its propositional nonexpansiveness theorem.
  Native and axiom-free on D63."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-monotone :as monotone]
            [rainbow.math.finite.bellman-optimal-contraction :as optimal]
            [rainbow.math.finite.bellman-value-optimality :as value-optimality]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.map-sum-respects :as map-respects]
            [rainbow.math.rational.nnrat.map-sum-scale :as map-scale]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def U [:param 'u])
(def V [:param 'v])
(def data-u [:succ U])
(def data-v [:succ V])
(def type-u [:sort data-u])
(def type-v [:sort data-v])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

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

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- total-mass [state states mass]
  (function/app (function/const* 'probability/nnrat-total-mass [U])
                state states mass))

(defn- expectation [state states mass value]
  (function/app (function/const* 'probability/nnrat-expectation [U])
                state states mass value))

(defn- rows-normalized [state action states transition]
  (function/app (function/const* 'markov/nnrat-rows-normalized [U V])
                state action states transition))

(defn- action-backup
  [state action states transition reward discount value current chosen]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount value current chosen))

(defn- backup-operator
  [state action states transition reward discount]
  (function/app
   (function/const* 'bellman/nnrat-action-backup [U V])
   state action states transition reward discount))

(defn- optimality-step
  [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))

(defn- equivalent-transitive [left middle right first-step second-step]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first-step second-step))

(defn- add-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app (function/const* 'nnrat/add-respects-equivalence [])
                left equivalent-left right equivalent-right
                same-left same-right))

(defn- action-backup-additive-upper-proof
  [lower-value upper-value epsilon pointwise state action row-normalized]
  (let [mass (function/app 'transition state action)
        reward-value (function/app 'reward state action)
        lower-expectation (expectation 'S 'states mass lower-value)
        upper-expectation (expectation 'S 'states mass upper-value)
        discounted-lower (multiply 'discount lower-expectation)
        discounted-upper (multiply 'discount upper-expectation)
        discounted-epsilon (multiply 'discount epsilon)
        discounted-shift
        (multiply 'discount (add upper-expectation epsilon))
        unfolded-lower (add reward-value discounted-lower)
        ordered-upper (add reward-value discounted-shift)
        target (add (add reward-value discounted-upper) discounted-epsilon)
        expectation-bound
        (function/app
         (function/const*
          'probability/nnrat-expectation-additive-upper-bound-normalized [U])
         'S 'states mass row-normalized
         lower-value upper-value epsilon pointwise)
        discounted-bound
        (function/app (function/const* 'nnrat/multiply-monotone [])
                      'discount lower-expectation
                      (add upper-expectation epsilon)
                      expectation-bound)
        reward-bound
        (function/app (function/const* 'nnrat/add-left-monotone [])
                      reward-value discounted-lower discounted-shift
                      discounted-bound)
        associate-target
        (function/app (function/const* 'nnrat/add-associative [])
                      reward-value discounted-upper discounted-epsilon)
        distribute-discount
        (function/app
         (function/const* 'nnrat/multiply-distributes-add-left [])
         'discount upper-expectation epsilon)
        collect-discount
        (add-respects
         reward-value reward-value
         (add discounted-upper discounted-epsilon) discounted-shift
         (equivalent-reflexive reward-value)
         (equivalent-symmetric
          discounted-shift
          (add discounted-upper discounted-epsilon)
          distribute-discount))
        target-is-upper
        (equivalent-transitive
         target
         (add reward-value (add discounted-upper discounted-epsilon))
         ordered-upper associate-target collect-discount)]
    (function/app
     (function/const* 'nnrat/at-most-respects-equivalence [])
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    lower-value state action)
     unfolded-lower
     (add
      (action-backup 'S 'A 'states 'transition 'reward 'discount
                     upper-value state action)
      discounted-epsilon)
     ordered-upper
     (equivalent-reflexive unfolded-lower)
     target-is-upper
     reward-bound)))

(def action-backup-contraction-spec
  (let [left-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'left-value 'state 'action)
        right-backup
        (action-backup 'S 'A 'states 'transition 'reward 'discount
                       'right-value 'state 'action)
        contracted-epsilon (multiply 'discount 'epsilon)
        left-to-right
        (at-most left-backup (add right-backup contracted-epsilon))
        right-to-left
        (at-most right-backup (add left-backup contracted-epsilon))]
    {:name 'bellman/nnrat-action-backup-contraction
     :universes ['u 'v]
     :type
     (function/forall
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['state 'S]
       ['action 'A]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states
                     (function/app 'transition 'state 'action))
         nnrat-one)]]
      (proposition/conjunction left-to-right right-to-left))
     :value
     (function/lam
      [['S type-u]
       ['A type-v]
       ['states (exact-finset-of U 'S)]
       ['transition (function/arrow 'S 'A 'S nnrat)]
       ['reward (function/arrow 'S 'A nnrat)]
       ['discount nnrat]
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['state 'S]
       ['action 'A]
       ['row-normalized
        (equivalent
         (total-mass 'S 'states
                     (function/app 'transition 'state 'action))
         nnrat-one)]]
      (function/app
       (function/const* 'proposition/conjoin [])
       left-to-right right-to-left
       (action-backup-additive-upper-proof
        'left-value 'right-value 'epsilon 'left-pointwise
        'state 'action 'row-normalized)
       (action-backup-additive-upper-proof
        'right-value 'left-value 'epsilon 'right-pointwise
        'state 'action 'row-normalized)))}))

(def optimality-step-sup-contraction-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        left-step
        (optimality-step 'S 'A 'actions 'fallback backup 'left-value 'state)
        right-step
        (optimality-step 'S 'A 'actions 'fallback backup 'right-value 'state)
        contracted-epsilon (multiply 'discount 'epsilon)
        left-to-right
        (at-most left-step (add right-step contracted-epsilon))
        right-to-left
        (at-most right-step (add left-step contracted-epsilon))]
    {:name 'value/nnrat-optimality-step-sup-contraction
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
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['state 'S]]
      (proposition/conjunction left-to-right right-to-left))
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
       ['left-value (function/arrow 'S nnrat)]
       ['right-value (function/arrow 'S nnrat)]
       ['epsilon nnrat]
       ['left-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'left-value 'next-state)
                  (add (function/app 'right-value 'next-state) 'epsilon)))]
       ['right-pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'right-value 'next-state)
                  (add (function/app 'left-value 'next-state) 'epsilon)))]
       ['normalized (rows-normalized 'S 'A 'states 'transition)]
       ['state 'S]]
      (let [left-backup
            (action-backup 'S 'A 'states 'transition 'reward 'discount
                           'left-value 'state 'action)
            right-backup
            (action-backup 'S 'A 'states 'transition 'reward 'discount
                           'right-value 'state 'action)
            action-left-to-right
            (at-most left-backup (add right-backup contracted-epsilon))
            action-right-to-left
            (at-most right-backup (add left-backup contracted-epsilon))
            action-contraction
            (function/lam
             [['action 'A]
              ['member (source-membership V 'A 'actions 'action)]]
             (function/app
              (function/const*
               'bellman/nnrat-action-backup-contraction [U V])
              'S 'A 'states 'transition 'reward 'discount
              'left-value 'right-value 'epsilon
              'left-pointwise 'right-pointwise 'state 'action
              (function/app 'normalized 'state 'action)))
            backup-left-to-right
            (function/lam
             [['action 'A]
              ['member (source-membership V 'A 'actions 'action)]]
             (left-conjunct
              action-left-to-right action-right-to-left
              (function/app action-contraction 'action 'member)))
            backup-right-to-left
            (function/lam
             [['action 'A]
              ['member (source-membership V 'A 'actions 'action)]]
             (right-conjunct
              action-left-to-right action-right-to-left
              (function/app action-contraction 'action 'member)))]
        (function/app
         (function/const*
          'value/nnrat-optimality-step-additively-nonexpansive [U V])
         'S 'A 'actions 'fallback 'fallback-admissible backup
         'left-value 'right-value contracted-epsilon 'state
         backup-left-to-right backup-right-to-left)))}))

(def theorem-specs
  [action-backup-contraction-spec
   optimality-step-sup-contraction-spec])

(def dependency-specs
  [value-optimality/total-mass-spec
   value-optimality/rows-normalized-spec
   value-optimality/multiply-distributes-add-left-spec
   value-optimality/expectation-add-constant-spec
   value-optimality/expectation-additive-upper-bound-normalized-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Finite Bellman backup contraction expression failed elaboration"
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
          {:origin :native :producer :finite-bellman-backup-contraction}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Finite Bellman backup contraction theorem was rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (let [base (-> checked-environment
                 monotone/extend-environment
                 optimal/extend-environment
                 map-respects/extend-environment
                 map-scale/extend-environment
                 multiply-commute/extend-environment)
        normalized-expectation-base
        (reduce add-spec base dependency-specs)]
    (reduce add-spec normalized-expectation-base theorem-specs)))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
