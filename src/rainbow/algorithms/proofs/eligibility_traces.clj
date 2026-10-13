(ns rainbow.algorithms.proofs.eligibility-traces
  "Eligibility traces (TD(lambda)) over exact rationals. Each state keeps a
  nonnegative eligibility trace that decays by the discount-times-lambda factor
  and is incremented when the state is visited: `e' = (gamma*lambda) * e + 1`. On
  a temporal-difference error the state value is updated in proportion to its
  trace: `value' = value + rate * trace * td-error`, spreading credit back over
  recently visited states (AHoF D63). The trace is a nonnegative rational and the
  update reuses signed scaling of the TD error.

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.eligibility-traces`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- trace-update [decay trace]
  (function/app (function/const* 'learning/eligibility-trace-update [])
                decay trace))
(defn- trace-weighted-update [rate trace td-error value]
  (function/app (function/const* 'learning/trace-weighted-update [])
                rate trace td-error value))

;; Definitions --------------------------------------------------------------

;; The eligibility trace decays and increments for the visited state.
(def trace-update-spec
  {:name 'learning/eligibility-trace-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['decay nnrat] ['trace nnrat]]
                        (nnrat-add (nnrat-multiply 'decay 'trace) nnrat-one))})

;; The trace-weighted value update: value plus rate*trace times the TD error.
(def trace-weighted-update-spec
  {:name 'learning/trace-weighted-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat signed signed signed)
   :value (function/lam [['rate nnrat] ['trace nnrat] ['td-error signed]
                         ['value signed]]
                        (signed-add 'value
                                    (signed-scale
                                     (nnrat-multiply 'rate 'trace)
                                     'td-error)))})

(def definition-specs [trace-update-spec trace-weighted-update-spec])

;; Theorems -----------------------------------------------------------------

(def trace-update-unfold-spec
  {:name 'learning/eligibility-trace-update-unfold :universes []
   :type (function/forall
          [['decay nnrat] ['trace nnrat]]
          (equality nnrat (trace-update 'decay 'trace)
                    (nnrat-add (nnrat-multiply 'decay 'trace) nnrat-one)))
   :value (function/lam [['decay nnrat] ['trace nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (trace-update 'decay 'trace)))})

(def trace-weighted-update-unfold-spec
  {:name 'learning/trace-weighted-update-unfold :universes []
   :type (function/forall
          [['rate nnrat] ['trace nnrat] ['td-error signed] ['value signed]]
          (equality signed
                    (trace-weighted-update 'rate 'trace 'td-error 'value)
                    (signed-add 'value
                                (signed-scale (nnrat-multiply 'rate 'trace)
                                              'td-error))))
   :value (function/lam [['rate nnrat] ['trace nnrat] ['td-error signed]
                         ['value signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (trace-weighted-update 'rate 'trace 'td-error
                                                       'value)))})

(def theorem-specs
  [trace-update-unfold-spec trace-weighted-update-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Eligibility-traces expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :eligibility-traces}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Eligibility-traces declaration rejected"
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
