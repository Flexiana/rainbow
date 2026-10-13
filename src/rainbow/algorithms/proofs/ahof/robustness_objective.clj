(ns rainbow.algorithms.proofs.ahof.robustness-objective
  "AHoF V13 worked robustness-based falsification objective over signed rationals.
  A satisfying trajectory has robustness 2 (positive); its falsification objective
  is -2 (negative). A violating trajectory has robustness -1 (negative); its
  objective is 1 (positive). So maximizing the objective favours the violating
  trajectory -- the falsification framing. The values are proved by signed
  cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.robustness-objective`
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
(def two (make-rational (data-nat 2) (data-nat 0)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-make [positive negative]
  (function/app (function/const* 'signed/make []) positive negative))
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

(def satisfying-robustness (function/const* 'ahof-v13/satisfying-robustness []))
(def violating-robustness (function/const* 'ahof-v13/violating-robustness []))

(defn- falsification-objective [robustness]
  (function/app (function/const* 'validation/falsification-objective [])
                robustness))

;; Definitions --------------------------------------------------------------

;; A satisfying trajectory: positive robustness 2.
(def satisfying-robustness-spec
  {:name 'ahof-v13/satisfying-robustness :kind :definition :universes []
   :type signed :value (from-nnrat two)})

;; A violating trajectory: negative robustness -1.
(def violating-robustness-spec
  {:name 'ahof-v13/violating-robustness :kind :definition :universes []
   :type signed
   :value (signed-make (function/const* 'nnrat/zero []) nnrat-one)})

(def definition-specs
  [satisfying-robustness-spec violating-robustness-spec])

;; Theorems -----------------------------------------------------------------

;; Satisfying robustness 2 maps to objective -2 (negative).
(def satisfying-objective-spec
  (let [objective (falsification-objective satisfying-robustness)
        at-neg-two (signed-make (function/const* 'nnrat/zero []) two)]
    {:name 'ahof-v13/satisfying-objective-is-negative-two :universes []
     :type (signed-equivalent objective at-neg-two)
     :value (signed-equivalent-cross objective at-neg-two)}))

;; Violating robustness -1 maps to objective 1 (positive).
(def violating-objective-spec
  (let [objective (falsification-objective violating-robustness)
        at-one (from-nnrat nnrat-one)]
    {:name 'ahof-v13/violating-objective-is-one :universes []
     :type (signed-equivalent objective at-one)
     :value (signed-equivalent-cross objective at-one)}))

(def robustness-objective-spec
  (let [satisfying-law (:type satisfying-objective-spec)
        violating-law (:type violating-objective-spec)]
    {:name 'ahof-v13/robustness-objective :universes []
     :type (proposition/conjunction satisfying-law violating-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      satisfying-law violating-law
      (function/const* 'ahof-v13/satisfying-objective-is-negative-two [])
      (function/const* 'ahof-v13/violating-objective-is-one []))}))

(def theorem-specs
  [satisfying-objective-spec violating-objective-spec
   robustness-objective-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF robustness-objective expression failed elaboration"
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
          {:origin :native :producer :ahof-v13-robustness-objective}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF robustness-objective declaration rejected"
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
