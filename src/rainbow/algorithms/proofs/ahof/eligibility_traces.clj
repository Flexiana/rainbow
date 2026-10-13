(ns rainbow.algorithms.proofs.ahof.eligibility-traces
  "AHoF D63 worked eligibility traces (TD(lambda)) over exact rationals. With a
  decay factor gamma*lambda = 1/2 and a current trace 1, the visited state's trace
  becomes (1/2)*1 + 1 = 3/2. With learning rate 1/2, a TD error 1, and a current
  value 0, the trace-weighted update raises the value by (1/2)*1 to 1/2. The trace
  and the updated value are proved by cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.eligibility-traces`
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
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def half (make-rational (data-nat 1) (data-nat 1)))
(def three-halves (make-rational (data-nat 3) (data-nat 1)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- nnrat-equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def decay (function/const* 'ahof-d63/decay []))
(def trace (function/const* 'ahof-d63/trace []))
(def rate (function/const* 'ahof-d63/rate []))
(def td-error (function/const* 'ahof-d63/td-error []))
(def value (function/const* 'ahof-d63/value []))

(defn- trace-update [d t]
  (function/app (function/const* 'learning/eligibility-trace-update []) d t))
(defn- trace-weighted-update [r t e v]
  (function/app (function/const* 'learning/trace-weighted-update []) r t e v))

;; Definitions --------------------------------------------------------------

(def decay-spec
  {:name 'ahof-d63/decay :kind :definition :universes []
   :type nnrat :value half})

(def trace-spec
  {:name 'ahof-d63/trace :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def rate-spec
  {:name 'ahof-d63/rate :kind :definition :universes []
   :type nnrat :value half})

(def td-error-spec
  {:name 'ahof-d63/td-error :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-one)})

(def value-spec
  {:name 'ahof-d63/value :kind :definition :universes []
   :type signed :value (from-nnrat (function/const* 'nnrat/zero []))})

(def updated-trace-spec
  {:name 'ahof-d63/updated-trace :kind :definition :universes []
   :type nnrat :value (trace-update decay trace)})

(def updated-value-spec
  {:name 'ahof-d63/updated-value :kind :definition :universes []
   :type signed :value (trace-weighted-update rate trace td-error value)})

(def definition-specs
  [decay-spec trace-spec rate-spec td-error-spec value-spec
   updated-trace-spec updated-value-spec])

;; Theorems -----------------------------------------------------------------

;; The visited state's trace becomes 3/2.
(def trace-is-three-halves-spec
  {:name 'ahof-d63/trace-is-three-halves :universes []
   :type (nnrat-equivalent (function/const* 'ahof-d63/updated-trace [])
                           three-halves)
   :value (nnrat-equivalent-cross (function/const* 'ahof-d63/updated-trace [])
                                  three-halves)})

;; The trace-weighted value update raises the value to 1/2.
(def value-is-one-half-spec
  {:name 'ahof-d63/value-is-one-half :universes []
   :type (signed-equivalent (function/const* 'ahof-d63/updated-value [])
                            (from-nnrat half))
   :value (signed-equivalent-cross (function/const* 'ahof-d63/updated-value [])
                                   (from-nnrat half))})

(def eligibility-traces-spec
  (let [trace-law (:type trace-is-three-halves-spec)
        value-law (:type value-is-one-half-spec)]
    {:name 'ahof-d63/eligibility-traces :universes []
     :type (proposition/conjunction trace-law value-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      trace-law value-law
      (function/const* 'ahof-d63/trace-is-three-halves [])
      (function/const* 'ahof-d63/value-is-one-half []))}))

(def theorem-specs
  [trace-is-three-halves-spec value-is-one-half-spec eligibility-traces-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF eligibility-traces expression failed elaboration"
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
          :rainbow/provenance
          {:origin :native :producer :ahof-d63-eligibility-traces}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF eligibility-traces declaration rejected"
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
