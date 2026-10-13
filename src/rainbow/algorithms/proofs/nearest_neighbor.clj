(ns rainbow.algorithms.proofs.nearest-neighbor
  "Nearest-neighbor value function approximation over exact rationals. Given two
  stored data points with their distances to a query and their stored values, the
  approximator returns the value of the nearer point (the one with the smaller
  distance), decided by exact rational comparison. This is the nonparametric value
  lookup of a nearest-neighbor approximator (AHoF D25): the approximated value at a
  query is the value carried by the closest data point, selected by a decidable
  distance comparison.

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.nearest-neighbor`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))

(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; A self-contained documentation proposition for the if-data condition slot.
(defn- condition [decision]
  (function/equality type-level bool decision decision))

(defn- if-value [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))

(defn- nearest-value [distance-a value-a distance-b value-b]
  (function/app (function/const* 'decision/nearest-value [])
                distance-a value-a distance-b value-b))

;; Definitions --------------------------------------------------------------

;; Return the value of the nearer point (smaller distance).
(def nearest-value-spec
  {:name 'decision/nearest-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['distance-a nnrat] ['value-a nnrat]
                         ['distance-b nnrat] ['value-b nnrat]]
                        (if-value (decide-at-most 'distance-a 'distance-b)
                                  'value-a 'value-b))})

(def definition-specs [nearest-value-spec])

;; Theorems -----------------------------------------------------------------

(def nearest-value-unfold-spec
  {:name 'decision/nearest-value-unfold :universes []
   :type (function/forall
          [['distance-a nnrat] ['value-a nnrat] ['distance-b nnrat]
           ['value-b nnrat]]
          (equality nnrat
                    (nearest-value 'distance-a 'value-a 'distance-b 'value-b)
                    (if-value (decide-at-most 'distance-a 'distance-b)
                              'value-a 'value-b)))
   :value (function/lam [['distance-a nnrat] ['value-a nnrat] ['distance-b nnrat]
                         ['value-b nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (nearest-value 'distance-a 'value-a 'distance-b
                                              'value-b)))})

(def theorem-specs [nearest-value-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nearest-neighbor expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :nearest-neighbor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nearest-neighbor declaration rejected"
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
