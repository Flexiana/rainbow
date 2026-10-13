(ns rainbow.algorithms.proofs.ahof.q-learning
  "AHoF D61 worked temporal-difference (Q-learning) update over signed rationals.

  A single state-action estimate starts overvalued at 1 with reward 0, discount
  0, and next value 0, so the temporal-difference error is -1: the estimate is
  too high. With learning rate 1/2 the first Q-values are 1, 1/2, 1/4, halving
  toward the true value 0. Proved native and axiom-free: the TD error is -1 and
  the values after one and two steps are 1/2 and 1/4. Convergence of the
  trajectory is not proved here. Only signed rationals make the negative
  temporal-difference error representable.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.q-learning`
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
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(def half (make-rational (data-nat 1) (data-nat 1)))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- signed-make [positive negative]
  (function/app (function/const* 'signed/make []) positive negative))

(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))

(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))

(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))

(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def rate (function/const* 'ahof-d61/rate []))
(def reward (function/const* 'ahof-d61/reward []))
(def discount (function/const* 'ahof-d61/discount []))
(def next-value (function/const* 'ahof-d61/next-value []))
(def initial (function/const* 'ahof-d61/initial []))

(defn- q-iterate [steps]
  (function/app (function/const* 'learning/signed-q-iterate [])
                rate reward discount next-value steps initial))

(def td-error
  (function/app (function/const* 'learning/signed-td-error [])
                reward discount next-value initial))

;; Definitions --------------------------------------------------------------

(def rate-spec
  {:name 'ahof-d61/rate :kind :definition :universes []
   :type nnrat :value half})

(def reward-spec
  {:name 'ahof-d61/reward :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-zero)})

(def discount-spec
  {:name 'ahof-d61/discount :kind :definition :universes []
   :type nnrat :value nnrat-zero})

(def next-value-spec
  {:name 'ahof-d61/next-value :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-zero)})

(def initial-spec
  {:name 'ahof-d61/initial :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-one)})

(def trajectory-spec
  {:name 'ahof-d61/trajectory :kind :definition :universes []
   :type (function/arrow nat signed)
   :value (function/lam [['steps nat]] (q-iterate 'steps))})

(def definition-specs
  [rate-spec reward-spec discount-spec next-value-spec initial-spec
   trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def td-error-is-negative-spec
  ;; The temporal-difference error of the overvalued estimate is exactly -1.
  (let [minus-one (signed-make nnrat-zero nnrat-one)]
    {:name 'ahof-d61/td-error-is-negative :universes []
     :type (signed-equivalent td-error minus-one)
     :value (signed-equivalent-cross td-error minus-one)}))

(def q-values-spec
  (let [q1 (q-iterate (data-nat 1))
        q2 (q-iterate (data-nat 2))
        at-half (from-nnrat half)
        at-quarter (from-nnrat (make-rational (data-nat 1) (data-nat 3)))
        eq-1 (signed-equivalent q1 at-half)
        eq-2 (signed-equivalent q2 at-quarter)]
    {:name 'ahof-d61/q-values :universes []
     :type (proposition/conjunction eq-1 eq-2)
     :value (function/app
             (function/const* 'proposition/conjoin [])
             eq-1 eq-2
             (signed-equivalent-cross q1 at-half)
             (signed-equivalent-cross q2 at-quarter))}))

(def q-learning-spec
  (let [negative (:type td-error-is-negative-spec)
        values (:type q-values-spec)]
    {:name 'ahof-d61/q-learning :universes []
     :type (proposition/conjunction negative values)
     :value (function/app
             (function/const* 'proposition/conjoin [])
             negative values
             (function/const* 'ahof-d61/td-error-is-negative [])
             (function/const* 'ahof-d61/q-values []))}))

(def theorem-specs
  [td-error-is-negative-spec q-values-spec q-learning-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF Q-learning expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-d61-q-learning}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF Q-learning declaration rejected"
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
