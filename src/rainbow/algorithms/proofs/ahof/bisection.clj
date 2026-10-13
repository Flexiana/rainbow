(ns rainbow.algorithms.proofs.ahof.bisection
  "AHoF O12 worked bisection bracket search over exact rationals. Starting from
  the bracket [0, 1], the probe midpoint is 1/2; keeping the lower half narrows to
  [0, 1/2], whose probe midpoint is 1/4 -- the interval and probe both halve.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bisection`
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
(def bool (function/const* 'data/Bool []))
(def bool-true (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-half (function/const* 'nnrat/half []))
(def nnrat-quarter (function/const* 'nnrat/quarter []))
(def bracket (function/app (function/const* 'data/Product [type-level type-level])
                           nnrat nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- pair [lo hi]
  (function/app (function/const* 'data/pair [type-level type-level])
                nnrat nnrat lo hi))

(defn- midpoint [lo hi]
  (function/app (function/const* 'search/bracket-midpoint []) lo hi))
(defn- narrow [keep-lower lo hi]
  (function/app (function/const* 'search/bisection-narrow []) keep-lower lo hi))

;; Definitions --------------------------------------------------------------

(def first-midpoint-spec
  {:name 'ahof-o12/first-midpoint :kind :definition :universes []
   :type nnrat :value (midpoint nnrat-zero nnrat-one)})

(def lower-bracket-spec
  {:name 'ahof-o12/lower-bracket :kind :definition :universes []
   :type bracket :value (narrow bool-true nnrat-zero nnrat-one)})

(def second-midpoint-spec
  {:name 'ahof-o12/second-midpoint :kind :definition :universes []
   :type nnrat :value (midpoint nnrat-zero nnrat-half)})

(def definition-specs
  [first-midpoint-spec lower-bracket-spec second-midpoint-spec])

;; Theorems -----------------------------------------------------------------

(def first-midpoint-is-half-spec
  {:name 'ahof-o12/first-midpoint-is-half :universes []
   :type (equivalent (function/const* 'ahof-o12/first-midpoint []) nnrat-half)
   :value (equivalent-cross (function/const* 'ahof-o12/first-midpoint [])
                            nnrat-half)})

;; Keeping the lower half narrows [0, 1] to [0, first-midpoint].
(def narrows-lower-spec
  {:name 'ahof-o12/narrows-to-lower-half :universes []
   :type (equality bracket
                   (narrow bool-true nnrat-zero nnrat-one)
                   (pair nnrat-zero (midpoint nnrat-zero nnrat-one)))
   :value (function/app
           (function/const* 'search/narrow-keeps-lower [])
           nnrat-zero nnrat-one
           (function/app (function/const* 'equality/reflexive [type-level])
                         bool bool-true))})

(def second-midpoint-is-quarter-spec
  {:name 'ahof-o12/second-midpoint-is-quarter :universes []
   :type (equivalent (function/const* 'ahof-o12/second-midpoint [])
                     nnrat-quarter)
   :value (equivalent-cross (function/const* 'ahof-o12/second-midpoint [])
                            nnrat-quarter)})

(def bisection-spec
  (let [half-law (:type first-midpoint-is-half-spec)
        narrow-law (:type narrows-lower-spec)
        quarter-law (:type second-midpoint-is-quarter-spec)]
    {:name 'ahof-o12/bisection :universes []
     :type (proposition/conjunction
            half-law (proposition/conjunction narrow-law quarter-law))
     :value (function/app
             (function/const* 'proposition/conjoin [])
             half-law (proposition/conjunction narrow-law quarter-law)
             (function/const* 'ahof-o12/first-midpoint-is-half [])
             (function/app
              (function/const* 'proposition/conjoin [])
              narrow-law quarter-law
              (function/const* 'ahof-o12/narrows-to-lower-half [])
              (function/const* 'ahof-o12/second-midpoint-is-quarter [])))}))

(def theorem-specs
  [first-midpoint-is-half-spec narrows-lower-spec
   second-midpoint-is-quarter-spec bisection-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF bisection expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-o12-bisection}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF bisection declaration rejected"
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
