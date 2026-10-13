(ns rainbow.math.finite.bellman-monotone
  "Monotonicity of finite nnrat expectations, Bellman action backups, and the
  Bellman optimality operator.  Native and axiom-free on the D63 checkpoint."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.value-iteration :as fvi]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as multiply-right-monotone]
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
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-u]) element))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U]) element source))

(defn- source-membership [level element source value]
  (function/app (function/const* 'finset-data/to-set [level])
                element source value))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nnrat-map-sum [U])
                element mapping source))

(defn- expectation [element source mass value]
  (function/app (function/const* 'probability/nnrat-expectation [U])
                element source mass value))

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

(defn- greedy-action [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-greedy-action [U V])
                state action actions fallback backup value current))

(defn- optimality-step [state action actions fallback backup value current]
  (function/app (function/const* 'value/nnrat-optimality-step [U V])
                state action actions fallback backup value current))

(def list-map-sum-monotone-spec
  {:name 'list/nnrat-map-sum-monotone
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['lower (function/arrow 'A nnrat)]
     ['upper (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['x 'A]]
       (at-most (function/app 'lower 'x) (function/app 'upper 'x)))]
     ['source (list-of 'A)]]
    (at-most (map-sum 'A 'lower 'source)
             (map-sum 'A 'upper 'source)))
   :value
   (function/lam
    [['A type-u]
     ['lower (function/arrow 'A nnrat)]
     ['upper (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['x 'A]]
       (at-most (function/app 'lower 'x) (function/app 'upper 'x)))]
     ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-u zero-level])
     'A
     (function/lam
      [['xs (list-of 'A)]]
      (at-most (map-sum 'A 'lower 'xs)
               (map-sum 'A 'upper 'xs)))
     (function/app (function/const* 'nnrat/at-most-reflexive []) nnrat-zero)
     (function/lam
      [['head 'A]
       ['tail (list-of 'A)]
       ['induction-hypothesis
        (at-most (map-sum 'A 'lower 'tail)
                 (map-sum 'A 'upper 'tail))]]
      (function/app
       (function/const* 'nnrat/add-monotone [])
       (function/app 'lower 'head)
       (function/app 'upper 'head)
       (map-sum 'A 'lower 'tail)
       (map-sum 'A 'upper 'tail)
       (function/app 'pointwise 'head)
       'induction-hypothesis))
     'source))})

(def expectation-monotone-spec
  {:name 'probability/nnrat-expectation-monotone
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['lower-value (function/arrow 'A nnrat)]
     ['upper-value (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['state 'A]]
       (at-most (function/app 'lower-value 'state)
                (function/app 'upper-value 'state)))]]
    (at-most (expectation 'A 'source 'mass 'lower-value)
             (expectation 'A 'source 'mass 'upper-value)))
   :value
   (function/lam
    [['A type-u]
     ['source (exact-finset-of U 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['lower-value (function/arrow 'A nnrat)]
     ['upper-value (function/arrow 'A nnrat)]
     ['pointwise
      (function/forall
       [['state 'A]]
       (at-most (function/app 'lower-value 'state)
                (function/app 'upper-value 'state)))]]
    (let [lower-mapping
          (function/lam
           [['state 'A]]
           (multiply (function/app 'lower-value 'state)
                     (function/app 'mass 'state)))
          upper-mapping
          (function/lam
           [['state 'A]]
           (multiply (function/app 'upper-value 'state)
                     (function/app 'mass 'state)))
          products-pointwise
          (function/lam
           [['state 'A]]
           (function/app
            (function/const* 'nnrat/multiply-right-monotone [])
            (function/app 'lower-value 'state)
            (function/app 'upper-value 'state)
            (function/app 'mass 'state)
            (function/app 'pointwise 'state)))]
      (function/app
       (function/const* 'list/nnrat-map-sum-monotone [U])
       'A lower-mapping upper-mapping products-pointwise
       (enumeration 'A 'source))))})

(def action-backup-monotone-spec
  {:name 'bellman/nnrat-action-backup-monotone
   :universes ['u 'v]
   :type
   (function/forall
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['lower-value (function/arrow 'S nnrat)]
     ['upper-value (function/arrow 'S nnrat)]
     ['pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'lower-value 'next-state)
                (function/app 'upper-value 'next-state)))]
     ['state 'S]
     ['action 'A]]
    (at-most
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'lower-value 'state 'action)
     (action-backup 'S 'A 'states 'transition 'reward 'discount
                    'upper-value 'state 'action)))
   :value
   (function/lam
    [['S type-u]
     ['A type-v]
     ['states (exact-finset-of U 'S)]
     ['transition (function/arrow 'S 'A 'S nnrat)]
     ['reward (function/arrow 'S 'A nnrat)]
     ['discount nnrat]
     ['lower-value (function/arrow 'S nnrat)]
     ['upper-value (function/arrow 'S nnrat)]
     ['pointwise
      (function/forall
       [['next-state 'S]]
       (at-most (function/app 'lower-value 'next-state)
                (function/app 'upper-value 'next-state)))]
     ['state 'S]
     ['action 'A]]
    (let [mass (function/app 'transition 'state 'action)
          lower-expectation (expectation 'S 'states mass 'lower-value)
          upper-expectation (expectation 'S 'states mass 'upper-value)
          expectation-ordered
          (function/app
           (function/const* 'probability/nnrat-expectation-monotone [U])
           'S 'states mass 'lower-value 'upper-value 'pointwise)
          discounted-ordered
          (function/app
           (function/const* 'nnrat/multiply-monotone [])
           'discount lower-expectation upper-expectation expectation-ordered)]
      (function/app
       (function/const* 'nnrat/add-left-monotone [])
       (function/app 'reward 'state 'action)
       (multiply 'discount lower-expectation)
       (multiply 'discount upper-expectation)
       discounted-ordered)))})

(def optimality-step-monotone-spec
  (let [backup
        (backup-operator 'S 'A 'states 'transition 'reward 'discount)
        selected
        (greedy-action 'S 'A 'actions 'fallback backup 'lower-value 'state)
        lower-step
        (optimality-step 'S 'A 'actions 'fallback backup 'lower-value 'state)
        selected-upper-backup
        (function/app backup 'upper-value 'state selected)
        upper-step
        (optimality-step 'S 'A 'actions 'fallback backup 'upper-value 'state)]
    {:name 'value/nnrat-optimality-step-monotone
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
       ['lower-value (function/arrow 'S nnrat)]
       ['upper-value (function/arrow 'S nnrat)]
       ['pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'lower-value 'next-state)
                  (function/app 'upper-value 'next-state)))]
       ['state 'S]]
      (at-most lower-step upper-step))
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
       ['lower-value (function/arrow 'S nnrat)]
       ['upper-value (function/arrow 'S nnrat)]
       ['pointwise
        (function/forall
         [['next-state 'S]]
         (at-most (function/app 'lower-value 'next-state)
                  (function/app 'upper-value 'next-state)))]
       ['state 'S]]
      (let [backup-ordered
            (function/app
             (function/const* 'bellman/nnrat-action-backup-monotone [U V])
             'S 'A 'states 'transition 'reward 'discount
             'lower-value 'upper-value 'pointwise 'state selected)
            selected-member
            (function/app
             (function/const* 'value/nnrat-greedy-action-is-admissible [U V])
             'S 'A 'actions 'fallback backup 'fallback-admissible
             'lower-value 'state)
            selected-dominated
            (function/app
             (function/const* 'value/nnrat-optimality-step-dominates [U V])
             'S 'A 'actions 'fallback backup 'upper-value 'state
             selected selected-member)]
        (function/app
         (function/const* 'nnrat/at-most-transitive [])
         lower-step selected-upper-backup upper-step
         backup-ordered selected-dominated)))}))

(def definition-specs [])
(def theorem-specs
  [list-map-sum-monotone-spec
   expectation-monotone-spec
   action-backup-monotone-spec
   optimality-step-monotone-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite Bellman monotonicity expression failed elaboration"
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
          {:origin :native :producer :finite-bellman-monotone}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite Bellman monotonicity declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (let [base (-> checked-environment fvi/extend-environment add-monotone/extend-environment multiply-monotone/extend-environment multiply-right-monotone/extend-environment)] (reduce add-spec base (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman-monotone))
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
