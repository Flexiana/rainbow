(ns rainbow.algorithms.proofs.ahof.nearest-neighbor
  "AHoF D25 worked nearest-neighbor value function approximation over exact
  rationals. Two stored data points carry values 3/4 and 1/4. When the query is
  nearer the first point (distance 1/4 versus 1/2) the approximated value is 3/4;
  when a second query is nearer the second point (distance 1/2 versus 1/4) the
  approximated value is 1/4. The approximation follows the nearest point, decided
  by exact rational distance comparison, proved by reflexivity of the decided
  comparison.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.nearest-neighbor`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def quarter (make-rational (data-nat 1) (data-nat 3)))
(def half (make-rational (data-nat 1) (data-nat 1)))
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- nearest-value [distance-a value-a distance-b value-b]
  (function/app (function/const* 'decision/nearest-value [])
                distance-a value-a distance-b value-b))

(def value-a (function/const* 'ahof-d25/value-a []))
(def value-b (function/const* 'ahof-d25/value-b []))

;; Definitions --------------------------------------------------------------

;; The two stored data-point values.
(def value-a-spec
  {:name 'ahof-d25/value-a :kind :definition :universes []
   :type nnrat :value three-quarters})

(def value-b-spec
  {:name 'ahof-d25/value-b :kind :definition :universes []
   :type nnrat :value quarter})

;; Query 1 is nearer point A: distances 1/4 (A) and 1/2 (B).
(def query-near-a-spec
  {:name 'ahof-d25/query-near-a :kind :definition :universes []
   :type nnrat :value (nearest-value quarter value-a half value-b)})

;; Query 2 is nearer point B: distances 1/2 (A) and 1/4 (B).
(def query-near-b-spec
  {:name 'ahof-d25/query-near-b :kind :definition :universes []
   :type nnrat :value (nearest-value half value-a quarter value-b)})

(def definition-specs
  [value-a-spec value-b-spec query-near-a-spec query-near-b-spec])

;; Theorems -----------------------------------------------------------------

;; A query nearer A approximates to A's value 3/4.
(def approximates-a-spec
  {:name 'ahof-d25/query-near-a-is-value-a :universes []
   :type (equality nnrat (function/const* 'ahof-d25/query-near-a []) value-a)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat value-a)})

;; A query nearer B approximates to B's value 1/4.
(def approximates-b-spec
  {:name 'ahof-d25/query-near-b-is-value-b :universes []
   :type (equality nnrat (function/const* 'ahof-d25/query-near-b []) value-b)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat value-b)})

(def nearest-neighbor-spec
  (let [near-a-law (:type approximates-a-spec)
        near-b-law (:type approximates-b-spec)]
    {:name 'ahof-d25/nearest-neighbor :universes []
     :type (proposition/conjunction near-a-law near-b-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      near-a-law near-b-law
      (function/const* 'ahof-d25/query-near-a-is-value-a [])
      (function/const* 'ahof-d25/query-near-b-is-value-b []))}))

(def theorem-specs
  [approximates-a-spec approximates-b-spec nearest-neighbor-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF nearest-neighbor expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d25-nearest-neighbor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF nearest-neighbor declaration rejected"
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
