(ns rainbow.algorithms.proofs.ahof.conjugate-gradient
  "AHoF O18 worked conjugate gradient over signed rationals with pair state.

  Step size 1/2, conjugate coefficient 1, gradient the identity, starting from
  position 2 and direction 1. The new direction is -gradient(2) + 1 * 1 =
  -2 + 1 = -1 (the remembered direction 1 is folded in), and the position moves
  2 + (1/2)(-1) = 3/2. Plain steepest descent would ignore the remembered
  direction; momentum would move the position by the full new direction rather
  than the half step. The signed values are proved by cross-product equivalence.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.conjugate-gradient`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(def two (make-rational (data-nat 2) (data-nat 0)))
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

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- state-pair [x d]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x d))
(defn- position [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- direction [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))

(def alpha (function/const* 'ahof-o18/alpha []))
(def beta (function/const* 'ahof-o18/beta []))
(def gradient (function/const* 'ahof-o18/gradient []))
(def initial (function/const* 'ahof-o18/initial []))

(defn- conjugate-iterate [steps start]
  (function/app (function/const* 'optimization/conjugate-iterate [])
                alpha beta gradient steps start))
(defn- conjugate-step [s]
  (function/app (function/const* 'optimization/conjugate-step [])
                alpha beta gradient s))

;; Definitions --------------------------------------------------------------

(def alpha-spec
  {:name 'ahof-o18/alpha :kind :definition :universes []
   :type nnrat :value half})

(def beta-spec
  {:name 'ahof-o18/beta :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def gradient-spec
  {:name 'ahof-o18/gradient :kind :definition :universes []
   :type (function/arrow signed signed)
   :value (function/lam [['point signed]] 'point)})

(def initial-spec
  {:name 'ahof-o18/initial :kind :definition :universes []
   :type state
   :value (state-pair (from-nnrat two) (from-nnrat nnrat-one))})

(def trajectory-spec
  {:name 'ahof-o18/trajectory :kind :definition :universes []
   :type (function/arrow nat state)
   :value (function/lam [['steps nat]] (conjugate-iterate 'steps initial))})

(def definition-specs
  [alpha-spec beta-spec gradient-spec initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def first-direction-spec
  (let [step-one (conjugate-iterate (data-nat 1) initial)
        at-neg-one (signed-make (function/const* 'nnrat/zero []) nnrat-one)]
    {:name 'ahof-o18/first-direction-is-negative-one :universes []
     :type (signed-equivalent (direction step-one) at-neg-one)
     :value (signed-equivalent-cross (direction step-one) at-neg-one)}))

(def first-position-spec
  (let [step-one (conjugate-iterate (data-nat 1) initial)
        at-three-halves (from-nnrat three-halves)]
    {:name 'ahof-o18/first-position-is-three-halves :universes []
     :type (signed-equivalent (position step-one) at-three-halves)
     :value (signed-equivalent-cross (position step-one) at-three-halves)}))

(def recurrence-spec
  (let [base-law (equality state
                           (conjugate-iterate (function/const* 'data/zero [])
                                              initial)
                           initial)
        step-law (equality state
                           (conjugate-iterate (data-nat 1) initial)
                           (conjugate-step initial))]
    {:name 'ahof-o18/conjugate-recurrence :universes []
     :type (proposition/conjunction base-law step-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law step-law
      (function/app
       (function/const* 'optimization/conjugate-iterate-zero [])
       alpha beta gradient initial)
      (function/app (function/const* 'equality/reflexive [type-level])
                    state (conjugate-iterate (data-nat 1) initial)))}))

(def conjugate-gradient-spec
  (let [direction-law (:type first-direction-spec)
        position-law (:type first-position-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o18/conjugate-gradient :universes []
     :type (proposition/conjunction
            direction-law (proposition/conjunction position-law recurrence))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      direction-law (proposition/conjunction position-law recurrence)
      (function/const* 'ahof-o18/first-direction-is-negative-one [])
      (function/app
       (function/const* 'proposition/conjoin [])
       position-law recurrence
       (function/const* 'ahof-o18/first-position-is-three-halves [])
       (function/const* 'ahof-o18/conjugate-recurrence [])))}))

(def theorem-specs
  [first-direction-spec first-position-spec recurrence-spec
   conjugate-gradient-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF conjugate-gradient expression failed elaboration"
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
          {:origin :native :producer :ahof-o18-conjugate-gradient}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF conjugate-gradient declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.conjugate-gradient))
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
