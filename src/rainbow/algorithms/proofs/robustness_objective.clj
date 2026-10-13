(ns rainbow.algorithms.proofs.robustness-objective
  "The robustness-based falsification objective over signed rationals. Signal
  temporal logic robustness is positive when a trajectory satisfies a
  specification and negative when it violates it. The falsification objective
  negates the robustness, so a satisfying trajectory has a negative objective and
  a violating trajectory has a positive one -- maximizing the objective drives the
  search toward the most-violating trajectory (AHoF V13). Negating twice recovers
  the robustness, so the objective loses no information."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- falsification-objective [robustness]
  (function/app (function/const* 'validation/falsification-objective [])
                robustness))

;; Definitions --------------------------------------------------------------

;; The falsification objective negates the robustness.
(def falsification-objective-spec
  {:name 'validation/falsification-objective :kind :definition :universes []
   :type (function/arrow signed signed)
   :value (function/lam [['robustness signed]] (signed-negate 'robustness))})

(def definition-specs [falsification-objective-spec])

;; Theorems -----------------------------------------------------------------

(def falsification-objective-unfold-spec
  {:name 'validation/falsification-objective-unfold :universes []
   :type (function/forall
          [['robustness signed]]
          (equality signed (falsification-objective 'robustness)
                    (signed-negate 'robustness)))
   :value (function/lam [['robustness signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (falsification-objective 'robustness)))})

;; Applying the objective twice recovers the robustness (the objective is an
;; involution up to equivalence).
(def falsification-objective-involution-spec
  {:name 'validation/falsification-objective-involution :universes []
   :type (function/forall
          [['robustness signed]]
          (signed-equivalent
           (falsification-objective (falsification-objective 'robustness))
           'robustness))
   :value (function/lam [['robustness signed]]
                        (function/app
                         (function/const* 'signed/negate-involutive [])
                         'robustness))})

(def theorem-specs
  [falsification-objective-unfold-spec
   falsification-objective-involution-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Robustness-objective expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :robustness-objective}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Robustness-objective declaration rejected"
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
