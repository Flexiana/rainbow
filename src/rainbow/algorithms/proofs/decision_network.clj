(ns rainbow.algorithms.proofs.decision-network
  "Decision network evaluation over exact rationals. A decision network combines a
  chance node (a finite probability distribution over outcomes) with a utility
  node (a payoff for each outcome); evaluating the network is taking the expected
  utility -- the probability-weighted sum of the utilities over the outcomes
  (AHoF D18). This reuses the finite exact-rational expectation engine, with the
  chance masses as the distribution and the utilities as the value function.

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.decision-network`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [zero-level]) element))
(defn- expectation [source mass value]
  (function/app (function/const* 'probability/nnrat-expectation [zero-level])
                nat source mass value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- network-value [outcomes probability utility]
  (function/app (function/const* 'decision/network-value [])
                outcomes probability utility))

;; Definitions --------------------------------------------------------------

;; Evaluate the decision network: the expected utility under the chance masses.
(def network-value-spec
  {:name 'decision/network-value :kind :definition :universes []
   :type (function/forall
          [['outcomes (exact-finset-of nat)]
           ['probability (function/arrow nat nnrat)]
           ['utility (function/arrow nat nnrat)]]
          nnrat)
   :value (function/lam
           [['outcomes (exact-finset-of nat)]
            ['probability (function/arrow nat nnrat)]
            ['utility (function/arrow nat nnrat)]]
           (expectation 'outcomes 'probability 'utility))})

(def definition-specs [network-value-spec])

;; Theorems -----------------------------------------------------------------

(def network-value-unfold-spec
  {:name 'decision/network-value-unfold :universes []
   :type (function/forall
          [['outcomes (exact-finset-of nat)]
           ['probability (function/arrow nat nnrat)]
           ['utility (function/arrow nat nnrat)]]
          (equality nnrat
                    (network-value 'outcomes 'probability 'utility)
                    (expectation 'outcomes 'probability 'utility)))
   :value (function/lam
           [['outcomes (exact-finset-of nat)]
            ['probability (function/arrow nat nnrat)]
            ['utility (function/arrow nat nnrat)]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (network-value 'outcomes 'probability 'utility)))})

(def theorem-specs [network-value-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Decision-network expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :decision-network}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Decision-network declaration rejected"
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
