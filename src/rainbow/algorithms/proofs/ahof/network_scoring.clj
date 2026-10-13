(ns rainbow.algorithms.proofs.ahof.network-scoring
  "AHoF D14 worked additive Bayesian-network scoring. Three nodes with local
  scores 1/2, 1/4, 1/4 give a decomposed network score of exactly 1.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.network-scoring`
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
(def nnrat-half (function/const* 'nnrat/half []))
(def nnrat-quarter (function/const* 'nnrat/quarter []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- decide-nat-equality [left right]
  (function/app (function/const* 'nat/decide-equality []) left right))
(defn- if-nnrat [condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat condition decision then-value else-value))

(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

(defn- cons-nat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nat head tail))
(def nil-nat (function/app (function/const* 'data/nil [type-level]) nat))

(def local (function/const* 'ahof-d14/local-score []))
(def nodes (function/const* 'ahof-d14/nodes []))

;; Definitions --------------------------------------------------------------

(def local-score-spec
  {:name 'ahof-d14/local-score :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam
           [['node nat]]
           (if-nnrat (nat-equality 'node (data-nat 1))
                     (decide-nat-equality 'node (data-nat 1))
                     nnrat-quarter
                     (if-nnrat (nat-equality 'node (data-nat 2))
                               (decide-nat-equality 'node (data-nat 2))
                               nnrat-quarter
                               nnrat-half)))})

(def nodes-spec
  {:name 'ahof-d14/nodes :kind :definition :universes []
   :type (function/app (function/const* 'data/List [type-level]) nat)
   :value (cons-nat (data-nat 0)
                    (cons-nat (data-nat 1) (cons-nat (data-nat 2) nil-nat)))})

(def score-spec
  {:name 'ahof-d14/score :kind :definition :universes []
   :type nnrat
   :value (function/app (function/const* 'scoring/nnrat-total-score [])
                        local nodes)})

(def definition-specs [local-score-spec nodes-spec score-spec])

;; Theorems -----------------------------------------------------------------

(def score-is-one-spec
  {:name 'ahof-d14/score-is-one :universes []
   :type (equivalent (function/const* 'ahof-d14/score []) nnrat-one)
   :value (equivalent-cross (function/const* 'ahof-d14/score []) nnrat-one)})

(def network-scoring-spec
  {:name 'ahof-d14/network-scoring :universes []
   :type (proposition/conjunction
          (:type score-is-one-spec)
          (equivalent (function/app local (data-nat 0)) nnrat-half))
   :value (function/app
           (function/const* 'proposition/conjoin [])
           (:type score-is-one-spec)
           (equivalent (function/app local (data-nat 0)) nnrat-half)
           (function/const* 'ahof-d14/score-is-one [])
           (equivalent-cross (function/app local (data-nat 0)) nnrat-half))})

(def theorem-specs [score-is-one-spec network-scoring-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF network-scoring expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d14-network-scoring}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF network-scoring declaration rejected"
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
