(ns rainbow.algorithms.proofs.ahof.bayesian-learning
  "AHoF D11 worked Bayesian parameter learning over exact rationals. Starting from
  a prior mass 1/2, the first datum has likelihood 3/2, updating the mass to
  1/2 * 3/2 = 3/4; the second datum has likelihood 4/3, updating the posterior to
  3/4 * 4/3 = 1. Folding the likelihoods through the prior gives the posterior
  mass, proved by cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bayesian-learning`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def half (make-rational (data-nat 1) (data-nat 1)))
(def three-halves (make-rational (data-nat 3) (data-nat 1)))
(def four-thirds (make-rational (data-nat 4) (data-nat 2)))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))

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

(defn- bayesian-update [mass likelihood]
  (function/app (function/const* 'estimation/bayesian-update []) mass likelihood))
(defn- bayesian-posterior [prior likelihood-a likelihood-b]
  (function/app (function/const* 'estimation/bayesian-posterior [])
                prior likelihood-a likelihood-b))

(def prior (function/const* 'ahof-d11/prior []))

;; Definitions --------------------------------------------------------------

(def prior-spec
  {:name 'ahof-d11/prior :kind :definition :universes []
   :type nnrat :value half})

(def first-update-spec
  {:name 'ahof-d11/first-update :kind :definition :universes []
   :type nnrat :value (bayesian-update prior three-halves)})

(def posterior-spec
  {:name 'ahof-d11/posterior :kind :definition :universes []
   :type nnrat :value (bayesian-posterior prior three-halves four-thirds)})

(def definition-specs [prior-spec first-update-spec posterior-spec])

;; Theorems -----------------------------------------------------------------

;; After the first datum the mass is 3/4.
(def first-update-is-three-quarters-spec
  {:name 'ahof-d11/first-update-is-three-quarters :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d11/first-update [])
                           three-quarters)
   :value (equivalent-cross (function/const* 'ahof-d11/first-update [])
                            three-quarters)})

;; After both data the posterior mass is 1.
(def posterior-is-one-spec
  {:name 'ahof-d11/posterior-is-one :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d11/posterior []) nnrat-one)
   :value (equivalent-cross (function/const* 'ahof-d11/posterior []) nnrat-one)})

(def bayesian-learning-spec
  (let [first-law (:type first-update-is-three-quarters-spec)
        posterior-law (:type posterior-is-one-spec)]
    {:name 'ahof-d11/bayesian-learning :universes []
     :type (proposition/conjunction first-law posterior-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      first-law posterior-law
      (function/const* 'ahof-d11/first-update-is-three-quarters [])
      (function/const* 'ahof-d11/posterior-is-one []))}))

(def theorem-specs
  [first-update-is-three-quarters-spec posterior-is-one-spec
   bayesian-learning-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF bayesian-learning expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d11-bayesian-learning}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF bayesian-learning declaration rejected"
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
