(ns rainbow.math.finite.bellman
  "Exact scaled finite transition rows and fixed-policy Bellman numerators."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def two (function/app successor one))
(def three (function/app successor two))
(def four (function/app successor three))
(def five (function/app successor four))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- expectation [level element source mass value]
  (function/app
   (function/const* 'probability/expectation-numerator [level])
   element source mass value))

(defn- row-total [level element source transition state]
  (function/app
   (function/const* 'markov/row-total [level])
   element source transition state))

(defn- bellman
  [level element scale source transition reward discount value state]
  (function/app
   (function/const* 'bellman/fixed-policy-numerator [level])
   element scale source transition reward discount value state))

(def row-total-spec
  {:name 'markov/row-total
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)] ['state 'A]]
    nat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)] ['state 'A]]
    (function/app
     (function/const* 'probability/weight-total [U])
     'A 'source (function/app 'transition 'state)))})

(def rows-normalized-spec
  {:name 'markov/rows-normalized-at
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)]]
    'Prop)
   :value
   (function/lam
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)]]
    (function/forall
     [['state 'A]]
     (equality (row-total U 'A 'source 'transition 'state) 'scale)))})

(def bellman-output-scale-spec
  {:name 'bellman/output-scale
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat)
   :value
   (function/lam
    [['scale nat]]
    (multiply 'scale (multiply 'scale 'scale)))})

(def fixed-policy-numerator-spec
  {:name 'bellman/fixed-policy-numerator
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)]
     ['reward (function/arrow 'A nat)]
     ['discount nat] ['value (function/arrow 'A nat)]]
    (function/arrow 'A nat))
   :value
   (function/lam
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nat)]
     ['reward (function/arrow 'A nat)]
     ['discount nat] ['value (function/arrow 'A nat)] ['state 'A]]
    (add
     (multiply (function/app 'reward 'state)
               (multiply 'scale 'scale))
     (multiply
      'discount
      (expectation U 'A 'source
                   (function/app 'transition 'state) 'value))))})

(def two-state-space-spec
  {:name 'or-example/two-state-space
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
   :value (function/app (function/const* 'finset-data/range []) two)})

(def uniform-mass-spec
  {:name 'or-example/uniform-mass
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat)
   :value (function/lam [['ignored nat]] one)})

(def uniform-transition-spec
  {:name 'or-example/uniform-transition
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value (function/lam [['ignored-state nat] ['ignored-next nat]] one)})

(def identity-value-spec
  {:name 'or-example/identity-value
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat)
   :value (function/lam [['state nat]] 'state)})

(def two-state-uniform-normalized-spec
  {:name 'probability/two-state-uniform-normalized
   :universes []
   :type
   (function/app
    (function/const* 'probability/normalized-at [zero-level])
    nat two (function/const* 'or-example/two-state-space [])
    (function/const* 'or-example/uniform-mass []))
   :value
   (function/app (function/const* 'equality/reflexive [type-level]) nat two)})

(def two-state-identity-expectation-spec
  (let [result
        (expectation
         zero-level nat (function/const* 'or-example/two-state-space [])
         (function/const* 'or-example/uniform-mass [])
         (function/const* 'or-example/identity-value []))]
    {:name 'probability/two-state-identity-expectation
     :universes []
     :type (equality result one)
     :value
     (function/app (function/const* 'equality/reflexive [type-level])
                   nat one)}))

(def two-state-rows-normalized-spec
  {:name 'markov/two-state-rows-normalized
   :universes []
   :type
   (function/app
    (function/const* 'markov/rows-normalized-at [zero-level])
    nat two (function/const* 'or-example/two-state-space [])
    (function/const* 'or-example/uniform-transition []))
   :value
   (function/lam
    [['state nat]]
    (function/app (function/const* 'equality/reflexive [type-level]) nat two))})

(def two-state-state-one-result-spec
  (let [result
        (bellman
         zero-level nat two (function/const* 'or-example/two-state-space [])
         (function/const* 'or-example/uniform-transition [])
         (function/const* 'or-example/identity-value []) one
         (function/const* 'or-example/identity-value []) one)]
    {:name 'bellman/two-state-state-one-result
     :universes []
     :type (equality result five)
     :value
     (function/app (function/const* 'equality/reflexive [type-level])
                   nat five)}))

(def bellman-zero-data-spec
  (let [zero-function (function/lam [['state 'A]] zero)
        result
        (bellman U 'A 'scale 'source 'transition
                 zero-function 'discount zero-function 'state)
        expected-zero
        (expectation U 'A 'source (function/app 'transition 'state)
                     zero-function)]
    {:name 'bellman/zero-data
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['discount nat] ['state 'A]]
      (equality result zero))
     :value
     (function/lam
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['discount nat] ['state 'A]]
      (let [expectation-zero
            (function/app
             (function/const* 'probability/expectation-zero [U])
             'A 'source (function/app 'transition 'state))
            multiply-expectation
            (function/app
             (function/const* 'equality/congruent-function
                              [type-level type-level])
             nat nat (function/lam [['value nat]]
                                   (multiply 'discount 'value))
             expected-zero zero expectation-zero)
            discount-zero
            (function/app (function/const* 'nat/times-zero []) 'discount)]
        (function/app
         (function/const* 'equality/transitive [type-level])
         nat
         (multiply 'discount expected-zero)
         (multiply 'discount zero) zero
         multiply-expectation discount-zero)))}))

(def bellman-zero-discount-spec
  (let [reward-term
        (multiply (function/app 'reward 'state)
                  (multiply 'scale 'scale))]
    {:name 'bellman/zero-discount
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)]
       ['value (function/arrow 'A nat)] ['state 'A]]
      (equality
       (bellman U 'A 'scale 'source 'transition 'reward zero 'value 'state)
       reward-term))
     :value
     (function/lam
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)]
       ['value (function/arrow 'A nat)] ['state 'A]]
      (function/app
       (function/const* 'algebra/nat-add-zero-right []) reward-term))}))

(def bellman-monotone-spec
  (let [left-expectation
        (expectation U 'A 'source (function/app 'transition 'state) 'left)
        right-expectation
        (expectation U 'A 'source (function/app 'transition 'state) 'right)
        reward-term
        (multiply (function/app 'reward 'state)
                  (multiply 'scale 'scale))
        left-continuation (multiply 'discount left-expectation)
        right-continuation (multiply 'discount right-expectation)]
    {:name 'bellman/fixed-policy-monotone
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['state 'A]]
         (at-most (function/app 'left 'state)
                  (function/app 'right 'state)))]
       ['state 'A]]
      (at-most
       (bellman U 'A 'scale 'source 'transition
                'reward 'discount 'left 'state)
       (bellman U 'A 'scale 'source 'transition
                'reward 'discount 'right 'state)))
     :value
     (function/lam
      [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nat)]
       ['reward (function/arrow 'A nat)] ['discount nat]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['ordered
        (function/forall
         [['state 'A]]
         (at-most (function/app 'left 'state)
                  (function/app 'right 'state)))]
       ['state 'A]]
      (let [expectation-ordered
            (function/app
             (function/const* 'probability/expectation-monotone [U])
             'A 'source (function/app 'transition 'state)
             'left 'right 'ordered)
            continuation-ordered
            (function/app
             (function/const* 'nat/multiply-left-monotone [])
             'discount left-expectation right-expectation
             expectation-ordered)]
        (function/app
         (function/const* 'nat/add-left-monotone [])
         reward-term left-continuation right-continuation
         continuation-ordered)))}))

(def definition-specs
  [row-total-spec rows-normalized-spec bellman-output-scale-spec
   fixed-policy-numerator-spec two-state-space-spec uniform-mass-spec
   uniform-transition-spec identity-value-spec])

(def theorem-specs
  [two-state-uniform-normalized-spec two-state-identity-expectation-spec
   two-state-rows-normalized-spec two-state-state-one-result-spec
   bellman-zero-data-spec bellman-zero-discount-spec bellman-monotone-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite Bellman expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-fixed-policy-bellman}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite Bellman declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (into definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.bellman))
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
