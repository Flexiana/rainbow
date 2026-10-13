(ns rainbow.algorithms.proofs.ahof.policy-evaluation
  "AHoF D20 specialization of bounded exact-rational policy evaluation.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.policy-evaluation`
  prints this classification."
  (:refer-clojure :exclude [denominator numerator])
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
(def three (function/app successor two))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-half (function/const* 'nnrat/half []))
(def value-function (function/arrow nat nnrat))

(defn- succ [value] (function/app successor value))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- bellman [value state]
  (function/app
   (function/const* 'bellman/nnrat-fixed-policy [zero-level])
   nat (function/const* 'or-example/two-state-space [])
   (function/const* 'or-example/nnrat-deterministic-transition [])
   (function/const* 'or-example/nnrat-identity-reward [])
   nnrat-half value state))

(defn- step []
  (function/lam
   [['ignored nat] ['previous-value value-function]]
   (function/lam [['state nat]] (bellman 'previous-value 'state))))

(defn- evaluate [steps]
  (function/app
   (function/const* 'data/Nat.rec [type-level])
   (function/lam [['ignored nat]] value-function)
   (function/const* 'or-example/nnrat-zero-value [])
   (step) steps))

(defn- row-total [state]
  (function/app
   (function/const* 'list/nnrat-map-sum [zero-level])
   nat
   (function/app
    (function/const* 'or-example/nnrat-deterministic-transition []) state)
   (function/app
    (function/const* 'finset-data/enumeration [zero-level])
    nat (function/const* 'or-example/two-state-space []))))

(def evaluator-spec
  {:name 'ahof-d20/evaluate
   :kind :definition :universes []
   :type (function/arrow nat value-function)
   :value (function/lam [['steps nat]] (evaluate 'steps))})

(def worked-value-spec
  {:name 'ahof-d20/worked-two-step-value
   :kind :definition :universes [] :type value-function
   :value (function/const* 'or-example/nnrat-two-step-value [])})

(def definition-specs [evaluator-spec worked-value-spec])

(def finite-horizon-recurrence-spec
  (let [initial (function/const* 'or-example/nnrat-zero-value [])
        base-law
        (function/forall
         [['state nat]]
         (function/equality type-level nnrat
                            (function/app (evaluate zero) 'state)
                            (function/app initial 'state)))
        successor-law
        (function/forall
         [['steps nat]]
         (function/equality
          type-level value-function
          (evaluate (succ 'steps))
          (function/app (step) 'steps (evaluate 'steps))))]
    {:name 'ahof-d20/finite-horizon-recurrence
     :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/lam
       [['state nat]]
       (function/app (function/const* 'equality/reflexive [type-level])
                     nnrat (function/app initial 'state)))
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'nat/recursor-successor-constant [zero-level])
        value-function initial (step) 'steps)))}))

(def normalized-transition-rows-spec
  (let [zero-law (equivalent (row-total zero) nnrat-one)
        one-law (equivalent (row-total one) nnrat-one)]
    {:name 'ahof-d20/normalized-transition-rows
     :universes []
     :type (proposition/conjunction zero-law one-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      zero-law one-law
      (function/app (function/const* 'nnrat/equivalent-reflexive [])
                    nnrat-one)
      (function/app (function/const* 'nnrat/equivalent-reflexive [])
                    nnrat-one))}))

(def one-step-value-spec
  (let [at-zero (function/app (evaluate one) zero)
        at-one (function/app (evaluate one) one)
        zero-law (equivalent at-zero nnrat-zero)
        one-law (equivalent at-one nnrat-one)]
    {:name 'ahof-d20/one-step-value
     :universes []
     :type (proposition/conjunction zero-law one-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      zero-law one-law
      (function/const* 'bellman/two-state-first-step-zero [])
      (function/const* 'bellman/two-state-first-step-one []))}))

(def two-step-value-spec
  {:name 'ahof-d20/two-step-value
   :universes []
   :type-from 'bellman/two-state-two-step-value-iteration
   :value
   (function/const* 'bellman/two-state-two-step-value-iteration [])})

(def policy-evaluation-spec
  (let [normalized
        (proposition/conjunction
         (equivalent (row-total zero) nnrat-one)
         (equivalent (row-total one) nnrat-one))
        recurrence (:type finite-horizon-recurrence-spec)
        one-step (:type one-step-value-spec)]
    {:name 'ahof-d20/policy-evaluation
     :universes []
     :type
     (proposition/conjunction
      normalized
      (proposition/conjunction recurrence one-step))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      normalized
      (proposition/conjunction recurrence one-step)
      (function/const* 'ahof-d20/normalized-transition-rows [])
      (function/app
       (function/const* 'proposition/conjoin [])
       recurrence one-step
       (function/const* 'ahof-d20/finite-horizon-recurrence [])
       (function/const* 'ahof-d20/one-step-value [])))}))

(def theorem-specs
  [finite-horizon-recurrence-spec normalized-transition-rows-spec
   one-step-value-spec two-step-value-spec policy-evaluation-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF policy-evaluation expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (if-let [source-name (:type-from spec)]
               (:rainbow/type
                (environment/declaration
                 checked-environment
                 (environment/resolve-id checked-environment source-name)))
               (elaborate! checked-environment (:type spec)))
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
          {:origin :native :producer :ahof-d20-policy-evaluation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF policy-evaluation declaration rejected"
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
