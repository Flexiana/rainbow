(ns rainbow.math.monte-carlo-estimation
  "Direct Monte Carlo estimation of a failure probability. Given a finite list of
  sample outcomes (a boolean flag per sample, true = failure), the empirical
  failure frequency is the count of failures over the sample size, an exact
  rational. The count reduces a boolean indicator over the list; the estimate is
  a nonnegative rational."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def nat-one (function/app (function/const* 'data/succ []) nat-zero))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool-list (function/app (function/const* 'data/List [type-level]) bool))

(defn- indicator [flag]
  (function/app (function/const* 'estimation/nnrat-indicator []) flag))
(defn- failure-count [samples]
  (function/app (function/const* 'estimation/failure-count []) samples))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Definitions --------------------------------------------------------------

(def indicator-spec
  {:name 'estimation/nnrat-indicator :kind :definition :universes []
   :type (function/arrow bool nat)
   :value (function/lam
           [['flag bool]]
           (function/app
            (function/const* 'data/Bool.rec [type-level])
            (function/lam [['ignored bool]] nat)
            nat-zero nat-one 'flag))})

(def failure-count-spec
  {:name 'estimation/failure-count :kind :definition :universes []
   :type (function/arrow bool-list nat)
   :value (function/lam
           [['samples bool-list]]
           (function/app
            (function/const* 'list/nat-map-sum [zero-level])
            bool (function/const* 'estimation/nnrat-indicator [])
            'samples))})

(def monte-carlo-frequency-spec
  {:name 'estimation/monte-carlo-frequency :kind :definition :universes []
   :type (function/arrow bool-list nat nnrat)
   :value (function/lam
           [['samples bool-list] ['size-predecessor nat]]
           (make-rational (failure-count 'samples) 'size-predecessor))})

(def definition-specs
  [indicator-spec failure-count-spec monte-carlo-frequency-spec])

;; Theorems -----------------------------------------------------------------

(def indicator-failure-spec
  {:name 'estimation/indicator-failure :universes []
   :type (equality nat (indicator (function/const* 'data/true [])) nat-one)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat nat-one)})

(def indicator-success-spec
  {:name 'estimation/indicator-success :universes []
   :type (equality nat (indicator (function/const* 'data/false [])) nat-zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat nat-zero)})

(def count-empty-spec
  {:name 'estimation/count-empty :universes []
   :type (equality nat
                   (failure-count
                    (function/app (function/const* 'data/nil [type-level])
                                  bool))
                   nat-zero)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat nat-zero)})

(def theorem-specs
  [indicator-failure-spec indicator-success-spec count-empty-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Monte-Carlo expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :monte-carlo-estimation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Monte-Carlo declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.monte-carlo-estimation))
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
