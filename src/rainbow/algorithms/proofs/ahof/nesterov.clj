(ns rainbow.algorithms.proofs.ahof.nesterov
  "AHoF O20 worked Nesterov accelerated momentum over signed rationals.

  Momentum coefficient 1, rate 1, and a position-dependent gradient (the positive
  part of the point), starting from position 1 and velocity 1. The look-ahead
  point is `1 + 1 * 1 = 2`, so the gradient there is 2 (not the 1 it would be at
  the current point), giving velocity `1 * 1 - 1 * 2 = -1` and position
  `1 + (-1) = 0`. Plain Polyak momentum, evaluating the gradient at the current
  point, would instead give velocity 0 and position 1 -- so the look-ahead
  genuinely changes the trajectory. The signed values are proved by cross-product
  equivalence.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.nesterov`
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
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- succ [value] (function/app (function/const* 'data/succ []) value))
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

(defn- state-pair [x v]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x v))
(defn- position [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- velocity [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))

(def beta (function/const* 'ahof-o20/beta []))
(def rate (function/const* 'ahof-o20/rate []))
(def gradient (function/const* 'ahof-o20/gradient []))
(def initial (function/const* 'ahof-o20/initial []))

(defn- nesterov-iterate [steps start]
  (function/app (function/const* 'optimization/nesterov-iterate [])
                beta rate gradient steps start))
(defn- nesterov-step [s]
  (function/app (function/const* 'optimization/nesterov-step [])
                beta rate gradient s))

;; Definitions --------------------------------------------------------------

(def beta-spec
  {:name 'ahof-o20/beta :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def rate-spec
  {:name 'ahof-o20/rate :kind :definition :universes []
   :type nnrat :value nnrat-one})

;; Position-dependent gradient: the positive part of the current point.
(def gradient-spec
  {:name 'ahof-o20/gradient :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['point signed]] (signed-positive 'point))})

(def initial-spec
  {:name 'ahof-o20/initial :kind :definition :universes []
   :type state
   :value (state-pair (from-nnrat nnrat-one) (from-nnrat nnrat-one))})

(def trajectory-spec
  {:name 'ahof-o20/trajectory :kind :definition :universes []
   :type (function/arrow nat state)
   :value (function/lam [['steps nat]] (nesterov-iterate 'steps initial))})

(def definition-specs
  [beta-spec rate-spec gradient-spec initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def first-velocity-spec
  (let [step-one (nesterov-iterate (data-nat 1) initial)
        at-neg-one (signed-make nnrat-zero nnrat-one)]
    {:name 'ahof-o20/first-velocity-is-negative-one :universes []
     :type (signed-equivalent (velocity step-one) at-neg-one)
     :value (signed-equivalent-cross (velocity step-one) at-neg-one)}))

(def first-position-spec
  (let [step-one (nesterov-iterate (data-nat 1) initial)
        at-zero (from-nnrat nnrat-zero)]
    {:name 'ahof-o20/first-position-is-zero :universes []
     :type (signed-equivalent (position step-one) at-zero)
     :value (signed-equivalent-cross (position step-one) at-zero)}))

;; The concrete recurrence: the first iterate is one step from the initial,
;; and zero steps is the initial. This carries the recurrence without the
;; budget-heavy abstract-step successor lemma.
(def recurrence-spec
  (let [base-law (equality state
                           (nesterov-iterate (function/const* 'data/zero [])
                                             initial)
                           initial)
        step-law (equality state
                           (nesterov-iterate (data-nat 1) initial)
                           (nesterov-step initial))]
    {:name 'ahof-o20/nesterov-recurrence :universes []
     :type (proposition/conjunction base-law step-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law step-law
      (function/app
       (function/const* 'optimization/nesterov-iterate-zero [])
       beta rate gradient initial)
      (function/app (function/const* 'equality/reflexive [type-level])
                    state (nesterov-iterate (data-nat 1) initial)))}))

(def nesterov-spec
  (let [velocity-law (:type first-velocity-spec)
        position-law (:type first-position-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o20/nesterov :universes []
     :type (proposition/conjunction
            velocity-law (proposition/conjunction position-law recurrence))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      velocity-law (proposition/conjunction position-law recurrence)
      (function/const* 'ahof-o20/first-velocity-is-negative-one [])
      (function/app
       (function/const* 'proposition/conjoin [])
       position-law recurrence
       (function/const* 'ahof-o20/first-position-is-zero [])
       (function/const* 'ahof-o20/nesterov-recurrence [])))}))

(def theorem-specs
  [first-velocity-spec first-position-spec recurrence-spec nesterov-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF nesterov expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-o20-nesterov}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF nesterov declaration rejected"
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
