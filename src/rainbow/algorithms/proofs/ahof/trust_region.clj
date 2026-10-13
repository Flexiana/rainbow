(ns rainbow.algorithms.proofs.ahof.trust-region
  "AHoF O16 worked trust region step acceptance over exact rationals.

  Threshold 1/2 and a descent candidate 0 against the current point 2. When the
  predicted reduction is matched (actual 1, predicted 1) the ratio is 1, which
  clears the threshold, so the step is accepted and the update moves to the
  candidate 0. When the model over-predicts (actual 1, predicted 4) the ratio is
  1/4, which fails the threshold, so the step is rejected and the update keeps the
  current point 2. The two decisions exercise both sides of the accept-or-reject
  branch, and are proved by reflexivity of the decided comparison.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.trust-region`
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
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def bool-false (function/const* 'data/false []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def half (make-rational (data-nat 1) (data-nat 1)))
(def four (make-rational (data-nat 4) (data-nat 0)))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-equality [left right]
  (function/equality type-level signed left right))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))

(defn- reduction-ratio [actual predicted]
  (function/app (function/const* 'decision/reduction-ratio []) actual predicted))
(defn- trust-accept [threshold ratio]
  (function/app (function/const* 'decision/trust-accept []) threshold ratio))
(defn- trust-region-update [accept candidate current]
  (function/app (function/const* 'decision/trust-region-update [])
                accept candidate current))

(def threshold (function/const* 'ahof-o16/threshold []))
(def candidate (function/const* 'ahof-o16/candidate []))
(def current (function/const* 'ahof-o16/current []))

;; Definitions --------------------------------------------------------------

(def threshold-spec
  {:name 'ahof-o16/threshold :kind :definition :universes []
   :type nnrat :value half})

(def candidate-spec
  {:name 'ahof-o16/candidate :kind :definition :universes []
   :type signed :value (from-nnrat (function/const* 'nnrat/zero []))})

(def current-spec
  {:name 'ahof-o16/current :kind :definition :universes []
   :type signed :value (from-nnrat (make-rational (data-nat 2) (data-nat 0)))})

;; Matched prediction: ratio 1 = 1 / 1.
(def accept-ratio-spec
  {:name 'ahof-o16/accept-ratio :kind :definition :universes []
   :type nnrat :value (reduction-ratio nnrat-one nnrat-one)})

;; Over-prediction: ratio 1/4 = 1 / 4.
(def reject-ratio-spec
  {:name 'ahof-o16/reject-ratio :kind :definition :universes []
   :type nnrat :value (reduction-ratio nnrat-one four)})

(def definition-specs
  [threshold-spec candidate-spec current-spec accept-ratio-spec
   reject-ratio-spec])

;; Theorems -----------------------------------------------------------------

(def accept-decision-spec
  {:name 'ahof-o16/accept-decision-is-true :universes []
   :type (bool-equality
          (trust-accept threshold (function/const* 'ahof-o16/accept-ratio []))
          bool-true)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool bool-true)})

(def reject-decision-spec
  {:name 'ahof-o16/reject-decision-is-false :universes []
   :type (bool-equality
          (trust-accept threshold (function/const* 'ahof-o16/reject-ratio []))
          bool-false)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool bool-false)})

;; Accepted step moves to the candidate.
(def accepts-candidate-spec
  {:name 'ahof-o16/accepted-step-is-candidate :universes []
   :type (signed-equality
          (trust-region-update
           (trust-accept threshold (function/const* 'ahof-o16/accept-ratio []))
           candidate current)
          candidate)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        signed candidate)})

;; Rejected step keeps the current point.
(def rejects-current-spec
  {:name 'ahof-o16/rejected-step-is-current :universes []
   :type (signed-equality
          (trust-region-update
           (trust-accept threshold (function/const* 'ahof-o16/reject-ratio []))
           candidate current)
          current)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        signed current)})

(def trust-region-spec
  (let [accept-law (:type accept-decision-spec)
        reject-law (:type reject-decision-spec)
        accepts-law (:type accepts-candidate-spec)
        rejects-law (:type rejects-current-spec)]
    {:name 'ahof-o16/trust-region :universes []
     :type (proposition/conjunction
            accept-law
            (proposition/conjunction
             reject-law
             (proposition/conjunction accepts-law rejects-law)))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      accept-law
      (proposition/conjunction
       reject-law (proposition/conjunction accepts-law rejects-law))
      (function/const* 'ahof-o16/accept-decision-is-true [])
      (function/app
       (function/const* 'proposition/conjoin [])
       reject-law (proposition/conjunction accepts-law rejects-law)
       (function/const* 'ahof-o16/reject-decision-is-false [])
       (function/app
        (function/const* 'proposition/conjoin [])
        accepts-law rejects-law
        (function/const* 'ahof-o16/accepted-step-is-candidate [])
        (function/const* 'ahof-o16/rejected-step-is-current []))))}))

(def theorem-specs
  [accept-decision-spec reject-decision-spec accepts-candidate-spec
   rejects-current-spec trust-region-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF trust-region expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-o16-trust-region}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF trust-region declaration rejected"
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
