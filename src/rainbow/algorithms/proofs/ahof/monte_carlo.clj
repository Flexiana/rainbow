(ns rainbow.algorithms.proofs.ahof.monte-carlo
  "AHoF V26 worked direct Monte Carlo failure-probability estimation. Four sample
  outcomes -- one failure and three successes -- give an empirical failure
  frequency of exactly 1/4.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.monte-carlo`
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
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def bool-false (function/const* 'data/false []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- cons-bool [head tail]
  (function/app (function/const* 'data/cons [type-level]) bool head tail))
(def nil-bool (function/app (function/const* 'data/nil [type-level]) bool))

(def samples (function/const* 'ahof-v26/samples []))
(def estimate (function/const* 'ahof-v26/estimate []))

(defn- failure-count [source]
  (function/app (function/const* 'estimation/failure-count []) source))

;; Definitions --------------------------------------------------------------

(def samples-spec
  {:name 'ahof-v26/samples :kind :definition :universes []
   :type (function/app (function/const* 'data/List [type-level]) bool)
   :value (cons-bool bool-true
                     (cons-bool bool-false
                                (cons-bool bool-false
                                           (cons-bool bool-false nil-bool))))})

(def estimate-spec
  {:name 'ahof-v26/estimate :kind :definition :universes []
   :type (function/const* 'nnrat/NonnegativeRational [])
   :value (function/app (function/const* 'estimation/monte-carlo-frequency [])
                        samples (data-nat 3))})

(def definition-specs [samples-spec estimate-spec])

;; Theorems -----------------------------------------------------------------

(def count-is-one-spec
  {:name 'ahof-v26/count-is-one :universes []
   :type (equality nat (failure-count samples) (data-nat 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (failure-count samples))})

(def estimate-is-quarter-spec
  (let [quarter (make-rational (data-nat 1) (data-nat 3))]
    {:name 'ahof-v26/estimate-is-quarter :universes []
     :type (equivalent estimate quarter)
     :value (function/app (function/const* 'equality/reflexive [type-level])
                          nat (multiply-nat (numerator estimate)
                                            (denominator quarter)))}))

(def monte-carlo-spec
  (let [count-law (:type count-is-one-spec)
        estimate-law (:type estimate-is-quarter-spec)]
    {:name 'ahof-v26/monte-carlo :universes []
     :type (proposition/conjunction count-law estimate-law)
     :value (function/app
             (function/const* 'proposition/conjoin [])
             count-law estimate-law
             (function/const* 'ahof-v26/count-is-one [])
             (function/const* 'ahof-v26/estimate-is-quarter []))}))

(def theorem-specs
  [count-is-one-spec estimate-is-quarter-spec monte-carlo-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF Monte-Carlo expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-v26-monte-carlo}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF Monte-Carlo declaration rejected"
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
