(ns rainbow.algorithms.proofs.ahof.decision-network
  "AHoF D18 worked decision network evaluation over exact rationals. A chance node
  has two outcomes with probabilities 3/4 and 1/4; the utility node pays 1 for the
  first outcome and 0 for the second. Evaluating the network is the expected
  utility 3/4 * 1 + 1/4 * 0 = 3/4. The value is proved by cross-product
  equivalence over the finite expectation.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.decision-network`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- numeral [value]
  (nth (iterate succ (function/const* 'data/zero [])) value))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def three-quarters (make-rational (numeral 3) (numeral 3)))
(def one-quarter (make-rational (numeral 1) (numeral 3)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; A two-case function on nat: value at 0, value at 1, else zero.
(defn- two-case [at-zero at-one]
  (function/lam
   [['outcome nat]]
   (function/app
    (function/const* 'data/Nat.rec [type-level])
    (function/lam [['ignored nat]] nnrat)
    at-zero
    (function/lam
     [['previous nat] ['ignored-utility nnrat]]
     (function/app
      (function/const* 'data/Nat.rec [type-level])
      (function/lam [['ignored nat]] nnrat)
      at-one
      (function/lam [['ignored-previous nat] ['ignored nnrat]] nnrat-zero)
      'previous))
    'outcome)))

(def outcome-space (function/const* 'ahof-d18/outcome-space []))
(def probability (function/const* 'ahof-d18/probability []))
(def utility (function/const* 'ahof-d18/utility []))

(defn- network-value [outcomes prob util]
  (function/app (function/const* 'decision/network-value [])
                outcomes prob util))

;; Definitions --------------------------------------------------------------

(def outcome-space-spec
  {:name 'ahof-d18/outcome-space :kind :definition :universes []
   :type (function/app (function/const* 'finset-data/Finset [zero-level]) nat)
   :value (function/app (function/const* 'finset-data/range []) (numeral 2))})

;; Chance node: probability 3/4 on outcome 0, 1/4 on outcome 1.
(def probability-spec
  {:name 'ahof-d18/probability :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (two-case three-quarters one-quarter)})

;; Utility node: payoff 1 on outcome 0, 0 on outcome 1.
(def utility-spec
  {:name 'ahof-d18/utility :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (two-case nnrat-one nnrat-zero)})

(def network-eu-spec
  {:name 'ahof-d18/network-eu :kind :definition :universes []
   :type nnrat
   :value (network-value outcome-space probability utility)})

(def definition-specs
  [outcome-space-spec probability-spec utility-spec network-eu-spec])

;; Theorems -----------------------------------------------------------------

;; The evaluated network has expected utility 3/4.
(def network-eu-is-three-quarters-spec
  {:name 'ahof-d18/network-eu-is-three-quarters :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d18/network-eu [])
                           three-quarters)
   :value (equivalent-cross (function/const* 'ahof-d18/network-eu [])
                            three-quarters)})

;; The utility node pays 1 on the first outcome.
(def utility-at-zero-is-one-spec
  (let [util-zero (function/app utility (function/const* 'data/zero []))]
    {:name 'ahof-d18/utility-at-zero-is-one :universes []
     :type (nnrat-equivalent util-zero nnrat-one)
     :value (equivalent-cross util-zero nnrat-one)}))

;; The utility node pays 0 on the second outcome.
(def utility-at-one-is-zero-spec
  (let [util-one (function/app utility (numeral 1))]
    {:name 'ahof-d18/utility-at-one-is-zero :universes []
     :type (nnrat-equivalent util-one nnrat-zero)
     :value (equivalent-cross util-one nnrat-zero)}))

(def decision-network-spec
  (let [eu-law (:type network-eu-is-three-quarters-spec)
        util-zero-law (:type utility-at-zero-is-one-spec)
        util-one-law (:type utility-at-one-is-zero-spec)]
    {:name 'ahof-d18/decision-network :universes []
     :type (proposition/conjunction
            eu-law (proposition/conjunction util-zero-law util-one-law))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      eu-law (proposition/conjunction util-zero-law util-one-law)
      (function/const* 'ahof-d18/network-eu-is-three-quarters [])
      (function/app
       (function/const* 'proposition/conjoin [])
       util-zero-law util-one-law
       (function/const* 'ahof-d18/utility-at-zero-is-one [])
       (function/const* 'ahof-d18/utility-at-one-is-zero [])))}))

(def theorem-specs
  [network-eu-is-three-quarters-spec utility-at-zero-is-one-spec
   utility-at-one-is-zero-spec decision-network-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF decision-network expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d18-decision-network}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF decision-network declaration rejected"
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
