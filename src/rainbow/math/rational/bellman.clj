(ns rainbow.math.rational.bellman
  "Finite fixed-policy Bellman evaluation over nonnegative rational proof data."
  (:refer-clojure :exclude [denominator numerator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
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
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-half (function/const* 'nnrat/half []))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))

(defn- if-data [level carrier condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [level])
                carrier condition decision then-value else-value))

(defn- expectation [level element source mass value]
  (function/app
   (function/const* 'probability/nnrat-expectation [level])
   element source mass value))

(defn- bellman [level element source transition reward discount value state]
  (function/app
   (function/const* 'bellman/nnrat-fixed-policy [level])
   element source transition reward discount value state))

(defn- expanded-bellman
  [level element source transition reward discount value state]
  (add
   (function/app reward state)
   (multiply
    discount
    (expectation level element source (function/app transition state) value))))

(defn- value-iterate
  [level element source transition reward discount steps initial]
  (function/app
   (function/const* 'bellman/nnrat-value-iterate [level])
   element source transition reward discount steps initial))

(def fixed-policy-spec
  {:name 'bellman/nnrat-fixed-policy
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nnrat)]
     ['reward (function/arrow 'A nnrat)]
     ['discount nnrat]
     ['value (function/arrow 'A nnrat)]]
    (function/arrow 'A nnrat))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nnrat)]
     ['reward (function/arrow 'A nnrat)]
     ['discount nnrat]
     ['value (function/arrow 'A nnrat)]
     ['state 'A]]
    (expanded-bellman
     U 'A 'source 'transition 'reward 'discount 'value 'state))})

(def value-iterate-spec
  {:name 'bellman/nnrat-value-iterate
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nnrat)]
     ['reward (function/arrow 'A nnrat)]
     ['discount nnrat]]
    (function/arrow nat (function/arrow 'A nnrat)
                    (function/arrow 'A nnrat)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['transition (function/arrow 'A 'A nnrat)]
     ['reward (function/arrow 'A nnrat)]
     ['discount nnrat] ['steps nat]
     ['initial (function/arrow 'A nnrat)]]
    (function/app
     (function/const* 'data/Nat.rec [data-level])
     (function/lam [['ignored nat]] (function/arrow 'A nnrat))
     'initial
     (function/lam
      [['previous-step nat]
       ['previous-value (function/arrow 'A nnrat)]]
      (function/lam
       [['state 'A]]
       (bellman U 'A 'source 'transition 'reward 'discount
                'previous-value 'state)))
     'steps))})

(def deterministic-transition-spec
  {:name 'or-example/nnrat-deterministic-transition
   :kind :definition
   :universes []
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['state nat] ['next-state nat]]
    (if-data
     type-level nnrat
     (nat-equality 'state 'next-state)
     (decide-nat-equality 'state 'next-state)
     nnrat-one nnrat-zero))})

(def identity-reward-spec
  {:name 'or-example/nnrat-identity-reward
   :kind :definition
   :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam [['state nat]] (make-rational 'state zero))})

(def zero-value-spec
  {:name 'or-example/nnrat-zero-value
   :kind :definition
   :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['ignored-state nat]] nnrat-zero)})

(def two-step-value-spec
  {:name 'or-example/nnrat-two-step-value
   :kind :definition
   :universes []
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['state nat]]
    (expanded-bellman
     zero-level nat
     (function/const* 'or-example/two-state-space [])
     (function/const* 'or-example/nnrat-deterministic-transition [])
     (function/const* 'or-example/nnrat-identity-reward [])
     nnrat-half
     (function/const* 'or-example/nnrat-step-one-value [])
     'state))})

(def step-one-value-spec
  {:name 'or-example/nnrat-step-one-value
   :kind :definition
   :universes []
   :type (function/arrow nat nnrat)
   :value
   (value-iterate
    zero-level nat
    (function/const* 'or-example/two-state-space [])
    (function/const* 'or-example/nnrat-deterministic-transition [])
    (function/const* 'or-example/nnrat-identity-reward [])
    nnrat-half one
    (function/const* 'or-example/nnrat-zero-value []))})

(def definition-specs
  [fixed-policy-spec value-iterate-spec deterministic-transition-spec
   identity-reward-spec zero-value-spec step-one-value-spec two-step-value-spec])

(defn- reflexive-equivalence [left right]
  (function/app
   (function/const* 'equality/reflexive [type-level])
   nat
   (multiply-nat (numerator left) (denominator right))))

(defn- closed-computation-spec [name expression expected]
  {:name name
   :universes []
   :type (equivalent expression expected)
   :value (reflexive-equivalence expression expected)})

(def first-step-zero-spec
  (closed-computation-spec
   'bellman/two-state-first-step-zero
   (function/app (function/const* 'or-example/nnrat-step-one-value []) zero)
   nnrat-zero))

(def first-step-one-spec
  (closed-computation-spec
   'bellman/two-state-first-step-one
   (function/app (function/const* 'or-example/nnrat-step-one-value []) one)
   nnrat-one))

(defn- compact-second-step [state]
  (expanded-bellman
   zero-level nat
   (function/const* 'or-example/two-state-space [])
   (function/const* 'or-example/nnrat-deterministic-transition [])
   (function/const* 'or-example/nnrat-identity-reward [])
   nnrat-half
   (function/const* 'or-example/nnrat-identity-reward [])
   state))

(def compact-second-step-zero-spec
  (closed-computation-spec
   'bellman/two-state-compact-second-step-zero
   (compact-second-step zero)
   nnrat-zero))

(def compact-second-step-one-spec
  (closed-computation-spec
   'bellman/two-state-compact-second-step-one
   (compact-second-step one)
   (make-rational three one)))

(def fixed-policy-congruent-spec
  (let [transition-equivalence
        (function/forall
         [['state 'A] ['next 'A]]
         (equivalent
          (function/app 'transition 'state 'next)
          (function/app 'equivalent-transition 'state 'next)))
        reward-equivalence
        (function/forall
         [['state 'A]]
         (equivalent (function/app 'reward 'state)
                     (function/app 'equivalent-reward 'state)))
        value-equivalence
        (function/forall
         [['state 'A]]
         (equivalent (function/app 'value 'state)
                     (function/app 'equivalent-value 'state)))]
    {:name 'bellman/nnrat-fixed-policy-congruent
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['value (function/arrow 'A nnrat)]
       ['equivalent-value (function/arrow 'A nnrat)]
       ['same-transition transition-equivalence]
       ['same-reward reward-equivalence]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['same-value value-equivalence]
       ['state 'A]]
      (equivalent
       (bellman U 'A 'source 'transition 'reward 'discount 'value 'state)
       (bellman U 'A 'source 'equivalent-transition 'equivalent-reward
                'equivalent-discount 'equivalent-value 'state)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['equivalent-transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['equivalent-reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['equivalent-discount nnrat]
       ['value (function/arrow 'A nnrat)]
       ['equivalent-value (function/arrow 'A nnrat)]
       ['same-transition transition-equivalence]
       ['same-reward reward-equivalence]
       ['same-discount (equivalent 'discount 'equivalent-discount)]
       ['same-value value-equivalence]
       ['state 'A]]
      (let [left-expectation
            (expectation U 'A 'source (function/app 'transition 'state) 'value)
            right-expectation
            (expectation
             U 'A 'source (function/app 'equivalent-transition 'state)
             'equivalent-value)
            same-expectation
            (function/app
             (function/const*
              'nnrat/finite-expectation-respects-equivalence [U])
             'A 'source
             (function/app 'transition 'state)
             (function/app 'equivalent-transition 'state)
             'value 'equivalent-value
             (function/lam
              [['next 'A]]
              (function/app 'same-transition 'state 'next))
             'same-value)
            same-continuation
            (function/app
             (function/const* 'nnrat/multiply-respects-equivalence [])
             'discount 'equivalent-discount
             left-expectation right-expectation
             'same-discount same-expectation)]
        (function/app
         (function/const* 'nnrat/add-respects-equivalence [])
         (function/app 'reward 'state)
         (function/app 'equivalent-reward 'state)
         (multiply 'discount left-expectation)
         (multiply 'equivalent-discount right-expectation)
         (function/app 'same-reward 'state)
         same-continuation)))}))

(def fixed-policy-unfold-spec
  (let [left
        (bellman U 'A 'source 'transition 'reward 'discount 'value 'state)
        right
        (expanded-bellman
         U 'A 'source 'transition 'reward 'discount 'value 'state)]
    {:name 'bellman/nnrat-fixed-policy-unfold
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['value (function/arrow 'A nnrat)]
       ['state 'A]]
      (function/equality type-level nnrat left right))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)]
       ['discount nnrat] ['value (function/arrow 'A nnrat)]
       ['state 'A]]
      (function/app
       (function/const* 'equality/reflexive [type-level]) nnrat left))}))

(def value-iterate-zero-spec
  (let [iterated
        (value-iterate U 'A 'source 'transition 'reward 'discount zero 'initial)]
    {:name 'bellman/nnrat-value-iterate-zero
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['initial (function/arrow 'A nnrat)] ['state 'A]]
      (function/equality
       type-level nnrat (function/app iterated 'state)
       (function/app 'initial 'state)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['transition (function/arrow 'A 'A nnrat)]
       ['reward (function/arrow 'A nnrat)] ['discount nnrat]
       ['initial (function/arrow 'A nnrat)] ['state 'A]]
      (function/app
       (function/const* 'equality/reflexive [type-level])
       nnrat (function/app 'initial 'state)))}))

(defn- example-source []
  (function/const* 'or-example/two-state-space []))

(defn- example-transition []
  (function/const* 'or-example/nnrat-deterministic-transition []))

(defn- example-reward []
  (function/const* 'or-example/nnrat-identity-reward []))

(defn- example-step-one []
  (function/const* 'or-example/nnrat-step-one-value []))

(defn- actual-second-step [state]
  (expanded-bellman
   zero-level nat (example-source) (example-transition) (example-reward)
   nnrat-half (example-step-one) state))

(defn- example-mass [state next-state]
  (function/app (example-transition) state next-state))

(defn- multiply-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app
   (function/const* 'nnrat/multiply-respects-equivalence [])
   left equivalent-left right equivalent-right same-left same-right))

(defn- add-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (function/app
   (function/const* 'nnrat/add-respects-equivalence [])
   left equivalent-left right equivalent-right same-left same-right))

(defn- example-expectation-equivalence
  "Composes the two already checked first-step results along the concrete
  enumeration.  This avoids unfolding a nested rational fold merely to
  rediscover those opaque results."
  [state]
  (let [actual-zero (function/app (example-step-one) zero)
        actual-one (function/app (example-step-one) one)
        reference-zero (function/app (example-reward) zero)
        reference-one (function/app (example-reward) one)
        mass-zero (example-mass state zero)
        mass-one (example-mass state one)
        actual-product-zero (multiply actual-zero mass-zero)
        actual-product-one (multiply actual-one mass-one)
        reference-product-zero (multiply reference-zero mass-zero)
        reference-product-one (multiply reference-one mass-one)
        same-mass-zero
        (function/app
         (function/const* 'nnrat/equivalent-reflexive []) mass-zero)
        same-mass-one
        (function/app
         (function/const* 'nnrat/equivalent-reflexive []) mass-one)
        same-product-zero
        (multiply-respects
         actual-zero reference-zero mass-zero mass-zero
         (function/const* 'bellman/two-state-first-step-zero [])
         same-mass-zero)
        same-product-one
        (multiply-respects
         actual-one reference-one mass-one mass-one
         (function/const* 'bellman/two-state-first-step-one [])
         same-mass-one)
        same-empty
        (function/app
         (function/const* 'nnrat/equivalent-reflexive []) nnrat-zero)
        same-tail
        (add-respects
         actual-product-one reference-product-one
         nnrat-zero nnrat-zero same-product-one same-empty)]
    (add-respects
     actual-product-zero reference-product-zero
     (add actual-product-one nnrat-zero)
     (add reference-product-one nnrat-zero)
     same-product-zero same-tail)))

(defn- example-expectations [state]
  [(expectation
    zero-level nat (example-source) (function/app (example-transition) state)
    (example-step-one))
   (expectation
    zero-level nat (example-source) (function/app (example-transition) state)
    (example-reward))])

(defn- expectation-equivalence-spec [name state]
  (let [[actual reference] (example-expectations state)]
    {:name name
     :universes []
     :type (equivalent actual reference)
     :value (example-expectation-equivalence state)}))

(def step-one-expectation-zero-spec
  (expectation-equivalence-spec
   'probability/two-state-step-one-expectation-zero zero))

(def step-one-expectation-one-spec
  (expectation-equivalence-spec
   'probability/two-state-step-one-expectation-one one))

(defn- continuation-equivalence-spec [name state same-expectation]
  (let [actual-expectation
        (first (example-expectations state))
        reference-expectation
        (second (example-expectations state))
        actual-continuation (multiply nnrat-half actual-expectation)
        reference-continuation (multiply nnrat-half reference-expectation)]
    {:name name
     :universes []
     :type (equivalent actual-continuation reference-continuation)
     :value
     (multiply-respects
      nnrat-half nnrat-half actual-expectation reference-expectation
      (function/app
       (function/const* 'nnrat/equivalent-reflexive []) nnrat-half)
      same-expectation)}))

(def second-continuation-zero-spec
  (continuation-equivalence-spec
   'bellman/two-state-second-continuation-zero-congruent
   zero
   (function/const* 'probability/two-state-step-one-expectation-zero [])))

(def second-continuation-one-spec
  (continuation-equivalence-spec
   'bellman/two-state-second-continuation-one-congruent
   one
   (function/const* 'probability/two-state-step-one-expectation-one [])))

(defn- actual-to-compact-second-step [state same-continuation]
  (let [actual-expectation (first (example-expectations state))
        reference-expectation (second (example-expectations state))
        reward-at-state (function/app (example-reward) state)
        actual-continuation (multiply nnrat-half actual-expectation)
        reference-continuation (multiply nnrat-half reference-expectation)]
    (add-respects
     reward-at-state reward-at-state
     actual-continuation reference-continuation
     (function/app
      (function/const* 'nnrat/equivalent-reflexive []) reward-at-state)
     same-continuation)))

(defn- transitive-equivalence
  [left middle right left-middle middle-right]
  (function/app
   (function/const* 'nnrat/equivalent-transitive [])
   left middle right left-middle middle-right))

(def second-step-zero-congruent-spec
  (let [actual (actual-second-step zero)
        compact (compact-second-step zero)]
    {:name 'bellman/two-state-second-step-zero-congruent
     :universes []
     :type (equivalent actual compact)
     :value
     (actual-to-compact-second-step
      zero
      (function/const*
       'bellman/two-state-second-continuation-zero-congruent []))}))

(def second-step-one-congruent-spec
  (let [actual (actual-second-step one)
        compact (compact-second-step one)]
    {:name 'bellman/two-state-second-step-one-congruent
     :universes []
     :type (equivalent actual compact)
     :value
     (actual-to-compact-second-step
      one
      (function/const*
       'bellman/two-state-second-continuation-one-congruent []))}))

(def two-state-two-step-value-iteration-spec
  (let [at-zero (actual-second-step zero)
        at-one (actual-second-step one)
        compact-zero (compact-second-step zero)
        compact-one (compact-second-step one)
        three-halves (make-rational three one)
        zero-result (equivalent at-zero nnrat-zero)
        one-result (equivalent at-one three-halves)
        ]
    {:name 'bellman/two-state-two-step-value-iteration
     :universes []
     :type (proposition/conjunction zero-result one-result)
     :value
     (function/lam
      [['result 'Prop]
       ['continue (function/arrow zero-result one-result 'result)]]
      (function/app
       'continue
       (transitive-equivalence
        at-zero compact-zero nnrat-zero
        (function/const* 'bellman/two-state-second-step-zero-congruent [])
        (function/const* 'bellman/two-state-compact-second-step-zero []))
       (transitive-equivalence
        at-one compact-one three-halves
        (function/const* 'bellman/two-state-second-step-one-congruent [])
        (function/const* 'bellman/two-state-compact-second-step-one []))))}))

(def theorem-specs
  [first-step-zero-spec first-step-one-spec
   compact-second-step-zero-spec compact-second-step-one-spec
   step-one-expectation-zero-spec step-one-expectation-one-spec
   second-continuation-zero-spec second-continuation-one-spec
   second-step-zero-congruent-spec second-step-one-congruent-spec
   fixed-policy-unfold-spec value-iterate-zero-spec fixed-policy-congruent-spec
   two-state-two-step-value-iteration-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Rational Bellman expression failed elaboration"
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
          {:origin :native :producer :rational-fixed-policy-bellman}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Rational Bellman declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (-> checked-environment extend-definitions extend-theorems))

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
