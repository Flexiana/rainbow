(ns rainbow.algorithms.proofs.bayesian-learning
  "Bayesian parameter learning over exact rationals. The posterior mass of a
  parameter is its prior mass folded through the data: each datum multiplies the
  running mass by that datum's likelihood, so `posterior = prior * L1 * L2 * ...`
  (up to normalization). This is the sequential Bayesian update (AHoF D11) --
  `(reduce bayesian-update prior data)` -- where a single update multiplies the
  current mass by a likelihood.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.bayesian-learning`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- bayesian-update [mass likelihood]
  (function/app (function/const* 'estimation/bayesian-update [])
                mass likelihood))
(defn- bayesian-posterior [prior likelihood-a likelihood-b]
  (function/app (function/const* 'estimation/bayesian-posterior [])
                prior likelihood-a likelihood-b))

;; Definitions --------------------------------------------------------------

;; A single Bayesian update multiplies the current mass by a likelihood.
(def bayesian-update-spec
  {:name 'estimation/bayesian-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['mass nnrat] ['likelihood nnrat]]
                        (nnrat-multiply 'mass 'likelihood))})

;; Folding two data likelihoods through the prior gives the posterior mass.
(def bayesian-posterior-spec
  {:name 'estimation/bayesian-posterior :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['prior nnrat] ['likelihood-a nnrat]
                         ['likelihood-b nnrat]]
                        (bayesian-update
                         (bayesian-update 'prior 'likelihood-a)
                         'likelihood-b))})

(def definition-specs [bayesian-update-spec bayesian-posterior-spec])

;; Theorems -----------------------------------------------------------------

(def bayesian-update-unfold-spec
  {:name 'estimation/bayesian-update-unfold :universes []
   :type (function/forall
          [['mass nnrat] ['likelihood nnrat]]
          (equality nnrat (bayesian-update 'mass 'likelihood)
                    (nnrat-multiply 'mass 'likelihood)))
   :value (function/lam [['mass nnrat] ['likelihood nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (bayesian-update 'mass 'likelihood)))})

(def bayesian-posterior-unfold-spec
  {:name 'estimation/bayesian-posterior-unfold :universes []
   :type (function/forall
          [['prior nnrat] ['likelihood-a nnrat] ['likelihood-b nnrat]]
          (equality nnrat
                    (bayesian-posterior 'prior 'likelihood-a 'likelihood-b)
                    (bayesian-update
                     (bayesian-update 'prior 'likelihood-a) 'likelihood-b)))
   :value (function/lam [['prior nnrat] ['likelihood-a nnrat]
                         ['likelihood-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (bayesian-posterior 'prior 'likelihood-a
                                                   'likelihood-b)))})

(def theorem-specs
  [bayesian-update-unfold-spec bayesian-posterior-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Bayesian-learning expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :bayesian-learning}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Bayesian-learning declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.bayesian-learning))
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
