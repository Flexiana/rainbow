(ns rainbow.algorithms.proofs.cross-validation
  "K-fold cross-validation mean over exact rationals. Given the per-fold scores of
  an evaluated model, the cross-validation estimate is their mean: the sum of the
  fold scores divided by the fold count. This composes the exact-rational list sum
  (map then reduce) with exact rational division (AHoF V4) -- averaging the folds
  is the aggregation that turns per-fold evaluations into a single estimate.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.cross-validation`
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
(def score-list (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- nnrat-divide [total count]
  (function/app (function/const* 'nnrat/divide []) total count))
(defn- score-total [scores]
  (function/app (function/const* 'list/nnrat-map-sum [zero-level])
                nnrat (function/lam [['score nnrat]] 'score) scores))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- cross-validation-mean [scores count]
  (function/app (function/const* 'validation/cross-validation-mean [])
                scores count))
(defn- cross-validation-total [scores]
  (function/app (function/const* 'validation/cross-validation-total []) scores))

;; Definitions --------------------------------------------------------------

;; The total of the fold scores: sum the identity over the score list.
(def cross-validation-total-spec
  {:name 'validation/cross-validation-total :kind :definition :universes []
   :type (function/arrow score-list nnrat)
   :value (function/lam [['scores score-list]] (score-total 'scores))})

;; The cross-validation estimate: the fold total divided by the fold count.
(def cross-validation-mean-spec
  {:name 'validation/cross-validation-mean :kind :definition :universes []
   :type (function/arrow score-list nnrat nnrat)
   :value (function/lam [['scores score-list] ['count nnrat]]
                        (nnrat-divide (cross-validation-total 'scores)
                                      'count))})

(def definition-specs
  [cross-validation-total-spec cross-validation-mean-spec])

;; Theorems -----------------------------------------------------------------

(def total-unfold-spec
  {:name 'validation/cross-validation-total-unfold :universes []
   :type (function/forall
          [['scores score-list]]
          (equality nnrat (cross-validation-total 'scores)
                    (score-total 'scores)))
   :value (function/lam [['scores score-list]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (cross-validation-total 'scores)))})

(def mean-unfold-spec
  {:name 'validation/cross-validation-mean-unfold :universes []
   :type (function/forall
          [['scores score-list] ['count nnrat]]
          (equality nnrat (cross-validation-mean 'scores 'count)
                    (nnrat-divide (cross-validation-total 'scores) 'count)))
   :value (function/lam [['scores score-list] ['count nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (cross-validation-mean 'scores 'count)))})

(def theorem-specs [total-unfold-spec mean-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Cross-validation expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :cross-validation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Cross-validation declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.cross-validation))
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
