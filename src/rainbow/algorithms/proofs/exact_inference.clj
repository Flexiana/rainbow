(ns rainbow.algorithms.proofs.exact-inference
  "Exact Bayesian inference by enumeration over a finite hidden variable.

  A marginal is the sum, over every value of a finite hidden variable, of the
  factored joint `likelihood * prior`. This is exactly the finite rational
  expectation engine, exposed here under the inference reading and connected to
  the explicit enumerated factored joint, which opens the Bayesian-network
  cone (AHoF D1-D16)."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- exact-finset-of [level element]
  (function/app (function/const* 'finset-data/Finset [level]) element))

(defn- enumeration [level element source]
  (function/app (function/const* 'finset-data/enumeration [level])
                element source))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- map-sum [level element mapping source]
  (function/app (function/const* 'list/nnrat-map-sum [level])
                element mapping source))

(defn- expectation [level element source mass value]
  (function/app (function/const* 'probability/nnrat-expectation [level])
                element source mass value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- joint [prior likelihood hidden]
  (function/app (function/const* 'inference/nnrat-joint [U])
                'H prior likelihood hidden))

(defn- marginal [grid prior likelihood]
  (function/app (function/const* 'inference/nnrat-marginal [U])
                'H grid prior likelihood))

;; Definitions --------------------------------------------------------------

(def joint-spec
  {:name 'inference/nnrat-joint
   :kind :definition :universes ['u]
   :type (function/forall
          [['H type-u]
           ['prior (function/arrow 'H nnrat)]
           ['likelihood (function/arrow 'H nnrat)]
           ['hidden 'H]]
          nnrat)
   :value (function/lam
           [['H type-u]
            ['prior (function/arrow 'H nnrat)]
            ['likelihood (function/arrow 'H nnrat)]
            ['hidden 'H]]
           (multiply (function/app 'likelihood 'hidden)
                     (function/app 'prior 'hidden)))})

(def marginal-spec
  {:name 'inference/nnrat-marginal
   :kind :definition :universes ['u]
   :type (function/forall
          [['H type-u] ['grid (exact-finset-of U 'H)]
           ['prior (function/arrow 'H nnrat)]
           ['likelihood (function/arrow 'H nnrat)]]
          nnrat)
   :value (function/lam
           [['H type-u] ['grid (exact-finset-of U 'H)]
            ['prior (function/arrow 'H nnrat)]
            ['likelihood (function/arrow 'H nnrat)]]
           (expectation U 'H 'grid 'prior 'likelihood))})

(def definition-specs [joint-spec marginal-spec])

;; Theorems -----------------------------------------------------------------

(def joint-unfold-spec
  {:name 'inference/nnrat-joint-unfold
   :universes ['u]
   :type (function/forall
          [['H type-u]
           ['prior (function/arrow 'H nnrat)]
           ['likelihood (function/arrow 'H nnrat)]
           ['hidden 'H]]
          (equality nnrat (joint 'prior 'likelihood 'hidden)
                    (multiply (function/app 'likelihood 'hidden)
                              (function/app 'prior 'hidden))))
   :value (function/lam
           [['H type-u]
            ['prior (function/arrow 'H nnrat)]
            ['likelihood (function/arrow 'H nnrat)]
            ['hidden 'H]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (joint 'prior 'likelihood 'hidden)))})

(def marginal-unfold-spec
  {:name 'inference/nnrat-marginal-unfold
   :universes ['u]
   :type (function/forall
          [['H type-u] ['grid (exact-finset-of U 'H)]
           ['prior (function/arrow 'H nnrat)]
           ['likelihood (function/arrow 'H nnrat)]]
          (equality nnrat (marginal 'grid 'prior 'likelihood)
                    (expectation U 'H 'grid 'prior 'likelihood)))
   :value (function/lam
           [['H type-u] ['grid (exact-finset-of U 'H)]
            ['prior (function/arrow 'H nnrat)]
            ['likelihood (function/arrow 'H nnrat)]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (marginal 'grid 'prior 'likelihood)))})

(def marginal-is-enumerated-joint-spec
  {:name 'inference/nnrat-marginal-is-enumerated-joint
   :universes ['u]
   :type (function/forall
          [['H type-u] ['grid (exact-finset-of U 'H)]
           ['prior (function/arrow 'H nnrat)]
           ['likelihood (function/arrow 'H nnrat)]]
          (equality nnrat (marginal 'grid 'prior 'likelihood)
                    (map-sum U 'H
                             (function/app
                              (function/const* 'inference/nnrat-joint [U])
                              'H 'prior 'likelihood)
                             (enumeration U 'H 'grid))))
   :value (function/lam
           [['H type-u] ['grid (exact-finset-of U 'H)]
            ['prior (function/arrow 'H nnrat)]
            ['likelihood (function/arrow 'H nnrat)]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (marginal 'grid 'prior 'likelihood)))})

(def marginal-transfer-spec
  (let [unfold
        (fn [likelihood]
          (equality nnrat (marginal 'grid 'prior likelihood)
                    (expectation U 'H 'grid 'prior likelihood)))]
    {:name 'inference/nnrat-marginal-transfer
     :universes ['u]
     :type (function/forall
            [['H type-u] ['grid (exact-finset-of U 'H)]
             ['prior (function/arrow 'H nnrat)]
             ['left-likelihood (function/arrow 'H nnrat)]
             ['right-likelihood (function/arrow 'H nnrat)]]
            (proposition/conjunction
             (unfold 'left-likelihood) (unfold 'right-likelihood)))
     :value (function/lam
             [['H type-u] ['grid (exact-finset-of U 'H)]
              ['prior (function/arrow 'H nnrat)]
              ['left-likelihood (function/arrow 'H nnrat)]
              ['right-likelihood (function/arrow 'H nnrat)]]
             (function/app
              (function/const* 'proposition/conjoin [])
              (unfold 'left-likelihood) (unfold 'right-likelihood)
              (function/app (function/const* 'equality/reflexive [type-level])
                            nnrat (marginal 'grid 'prior 'left-likelihood))
              (function/app (function/const* 'equality/reflexive [type-level])
                            nnrat (marginal 'grid 'prior 'right-likelihood))))}))

(def theorem-specs
  [joint-unfold-spec marginal-unfold-spec marginal-is-enumerated-joint-spec
   marginal-transfer-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Exact-inference expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :exact-inference}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Exact-inference declaration rejected"
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
