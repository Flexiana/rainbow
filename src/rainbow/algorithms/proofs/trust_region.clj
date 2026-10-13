(ns rainbow.algorithms.proofs.trust-region
  "Trust region step acceptance over exact rationals. A trust region method
  computes the ratio of the actual reduction to the predicted reduction, and
  accepts the candidate step only when that ratio clears a threshold; otherwise
  it rejects the step and keeps the current point (and would shrink the region).
  The accept-or-reject branch is the distinctive control flow of trust region
  methods (AHoF O16): `reduction-ratio` uses exact rational division,
  `trust-accept?` decides the threshold comparison, and `trust-region-update`
  selects the candidate or the current point by that decision.

  Scope (measured by the kernel): this module has 4 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.trust-region`
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
(def signed (function/const* 'signed/SignedRational []))

(defn- nnrat-divide [actual predicted]
  (function/app (function/const* 'nnrat/divide []) actual predicted))
(defn- decide-at-most [left right]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; A self-contained documentation proposition for the if-data condition slot.
(defn- condition [decision]
  (function/equality type-level bool decision decision))

(defn- if-signed [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                signed (condition decision) decision then-value else-value))

(defn- reduction-ratio [actual predicted]
  (function/app (function/const* 'decision/reduction-ratio []) actual predicted))
(defn- trust-accept [threshold ratio]
  (function/app (function/const* 'decision/trust-accept []) threshold ratio))
(defn- trust-region-update [accept candidate current]
  (function/app (function/const* 'decision/trust-region-update [])
                accept candidate current))

;; Definitions --------------------------------------------------------------

;; The reduction ratio: actual reduction over predicted reduction.
(def reduction-ratio-spec
  {:name 'decision/reduction-ratio :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['actual nnrat] ['predicted nnrat]]
                        (nnrat-divide 'actual 'predicted))})

;; Accept the step when the threshold is at most the ratio.
(def trust-accept-spec
  {:name 'decision/trust-accept :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['threshold nnrat] ['ratio nnrat]]
                        (decide-at-most 'threshold 'ratio))})

;; Select the candidate step if accepted, otherwise keep the current point.
(def trust-region-update-spec
  {:name 'decision/trust-region-update :kind :definition :universes []
   :type (function/arrow bool signed signed signed)
   :value (function/lam [['accept bool] ['candidate signed] ['current signed]]
                        (if-signed 'accept 'candidate 'current))})

(def definition-specs
  [reduction-ratio-spec trust-accept-spec trust-region-update-spec])

;; Theorems -----------------------------------------------------------------

(def reduction-ratio-unfold-spec
  {:name 'decision/reduction-ratio-unfold :universes []
   :type (function/forall
          [['actual nnrat] ['predicted nnrat]]
          (equality nnrat (reduction-ratio 'actual 'predicted)
                    (nnrat-divide 'actual 'predicted)))
   :value (function/lam [['actual nnrat] ['predicted nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (reduction-ratio 'actual 'predicted)))})

(def trust-accept-unfold-spec
  {:name 'decision/trust-accept-unfold :universes []
   :type (function/forall
          [['threshold nnrat] ['ratio nnrat]]
          (equality bool (trust-accept 'threshold 'ratio)
                    (decide-at-most 'threshold 'ratio)))
   :value (function/lam [['threshold nnrat] ['ratio nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (trust-accept 'threshold 'ratio)))})

;; When accepted (decision true), the update yields the candidate.
(def update-accepts-spec
  (let [true-const (function/const* 'data/true [])]
    {:name 'decision/trust-region-update-accepts :universes []
     :type (function/forall
            [['candidate signed] ['current signed]
             ['accepted (equality bool true-const true-const)]]
            (equality signed
                      (trust-region-update true-const 'candidate 'current)
                      'candidate))
     :value (function/lam
             [['candidate signed] ['current signed]
              ['accepted (equality bool true-const true-const)]]
             (function/app
              (function/const* 'equality/reflexive [type-level])
              signed 'candidate))}))

;; When rejected (decision false), the update keeps the current point.
(def update-rejects-spec
  (let [false-const (function/const* 'data/false [])]
    {:name 'decision/trust-region-update-rejects :universes []
     :type (function/forall
            [['candidate signed] ['current signed]
             ['rejected (equality bool false-const false-const)]]
            (equality signed
                      (trust-region-update false-const 'candidate 'current)
                      'current))
     :value (function/lam
             [['candidate signed] ['current signed]
              ['rejected (equality bool false-const false-const)]]
             (function/app
              (function/const* 'equality/reflexive [type-level])
              signed 'current))}))

(def theorem-specs
  [reduction-ratio-unfold-spec trust-accept-unfold-spec
   update-accepts-spec update-rejects-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Trust-region expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :trust-region}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Trust-region declaration rejected"
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
