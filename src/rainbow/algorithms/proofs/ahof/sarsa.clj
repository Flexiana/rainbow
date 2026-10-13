(ns rainbow.algorithms.proofs.ahof.sarsa
  "AHoF D62 worked SARSA on-policy update over signed rationals. With learning
  rate 1/2, reward 1, discount 1, an on-policy next action value 0, and a current
  action value 0, the TD error is (1 + 1*0) - 0 = 1, and the SARSA update raises
  the value to 0 + (1/2)*1 = 1/2. The updated value is proved by signed
  cross-product equivalence, and the update is shown to coincide with the shared
  Q-update on the same bootstrap value.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.sarsa`
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
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def half (make-rational (data-nat 1) (data-nat 1)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(def rate (function/const* 'ahof-d62/rate []))
(def reward (function/const* 'ahof-d62/reward []))
(def discount (function/const* 'ahof-d62/discount []))
(def next-value (function/const* 'ahof-d62/next-value []))
(def current (function/const* 'ahof-d62/current []))

(defn- sarsa-update [r rw d nx cur]
  (function/app (function/const* 'learning/signed-sarsa-update []) r rw d nx cur))
(defn- q-update [r rw d nx cur]
  (function/app (function/const* 'learning/signed-q-update []) r rw d nx cur))

;; Definitions --------------------------------------------------------------

(def rate-spec
  {:name 'ahof-d62/rate :kind :definition :universes []
   :type nnrat :value half})

(def reward-spec
  {:name 'ahof-d62/reward :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-one)})

(def discount-spec
  {:name 'ahof-d62/discount :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def next-value-spec
  {:name 'ahof-d62/next-value :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-zero)})

(def current-spec
  {:name 'ahof-d62/current :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-zero)})

(def updated-spec
  {:name 'ahof-d62/updated :kind :definition :universes []
   :type signed
   :value (sarsa-update rate reward discount next-value current)})

(def definition-specs
  [rate-spec reward-spec discount-spec next-value-spec current-spec
   updated-spec])

;; Theorems -----------------------------------------------------------------

;; The SARSA-updated action value is 1/2.
(def updated-is-one-half-spec
  {:name 'ahof-d62/updated-is-one-half :universes []
   :type (signed-equivalent (function/const* 'ahof-d62/updated [])
                            (from-nnrat half))
   :value (signed-equivalent-cross (function/const* 'ahof-d62/updated [])
                                   (from-nnrat half))})

;; On this bootstrap the SARSA update coincides with the Q-update.
(def coincides-with-q-update-spec
  {:name 'ahof-d62/coincides-with-q-update :universes []
   :type (equality signed
                   (sarsa-update rate reward discount next-value current)
                   (q-update rate reward discount next-value current))
   :value (function/app
           (function/const* 'learning/signed-sarsa-equals-q-update [])
           rate reward discount next-value current)})

(def sarsa-spec
  (let [updated-law (:type updated-is-one-half-spec)
        coincide-law (:type coincides-with-q-update-spec)]
    {:name 'ahof-d62/sarsa :universes []
     :type (proposition/conjunction updated-law coincide-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      updated-law coincide-law
      (function/const* 'ahof-d62/updated-is-one-half [])
      (function/const* 'ahof-d62/coincides-with-q-update []))}))

(def theorem-specs
  [updated-is-one-half-spec coincides-with-q-update-spec sarsa-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF SARSA expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d62-sarsa}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF SARSA declaration rejected"
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
