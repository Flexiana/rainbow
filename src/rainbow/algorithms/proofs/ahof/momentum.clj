(ns rainbow.algorithms.proofs.ahof.momentum
  "AHoF O19 worked Polyak momentum over signed rationals with pair state.

  Momentum coefficient 1 and rate 1 with a constant unit gradient, starting from
  position 0 and velocity 2. One step gives velocity `1 * 2 - 1 * 1 = 1` and
  position `0 + 1 = 1`: the momentum term `1 * 2 = 2` carries the previous
  velocity, which plain gradient descent lacks. The signed values are proved by
  cross-product equivalence; the recurrence is the generic iterate zero/successor.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.momentum`
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
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))
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
(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

;; signed/equivalent unfolds to Eq nat over positive+negative cross sums.
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

(def beta (function/const* 'ahof-o19/beta []))
(def rate (function/const* 'ahof-o19/rate []))
(def gradient (function/const* 'ahof-o19/gradient []))
(def initial (function/const* 'ahof-o19/initial []))

(defn- momentum-iterate [steps start]
  (function/app (function/const* 'optimization/momentum-iterate [])
                beta rate gradient steps start))

;; Definitions --------------------------------------------------------------

(def beta-spec
  {:name 'ahof-o19/beta :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def rate-spec
  {:name 'ahof-o19/rate :kind :definition :universes []
   :type nnrat :value nnrat-one})

(def gradient-spec
  {:name 'ahof-o19/gradient :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['ignored-point signed]] nnrat-one)})

(def initial-spec
  {:name 'ahof-o19/initial :kind :definition :universes []
   :type state
   :value (state-pair (from-nnrat (function/const* 'nnrat/zero []))
                      (from-nnrat two))})

(def trajectory-spec
  {:name 'ahof-o19/trajectory :kind :definition :universes []
   :type (function/arrow nat state)
   :value (function/lam [['steps nat]] (momentum-iterate 'steps initial))})

(def definition-specs
  [beta-spec rate-spec gradient-spec initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def first-velocity-spec
  (let [step-one (momentum-iterate (data-nat 1) initial)
        at-one (from-nnrat nnrat-one)]
    {:name 'ahof-o19/first-velocity-is-one :universes []
     :type (signed-equivalent (velocity step-one) at-one)
     :value (signed-equivalent-cross (velocity step-one) at-one)}))

(def first-position-spec
  (let [step-one (momentum-iterate (data-nat 1) initial)
        at-one (from-nnrat nnrat-one)]
    {:name 'ahof-o19/first-position-is-one :universes []
     :type (signed-equivalent (position step-one) at-one)
     :value (signed-equivalent-cross (position step-one) at-one)}))

(def recurrence-spec
  (let [sequence (fn [steps] (momentum-iterate steps initial))
        step (function/lam
              [['step-index nat] ['previous state]]
              (function/app (function/const* 'optimization/momentum-step [])
                            beta rate gradient 'previous))
        base-law (equality state
                           (sequence (function/const* 'data/zero [])) initial)
        successor-law
        (function/forall
         [['steps nat]]
         (equality state (sequence (succ 'steps))
                   (function/app step 'steps (sequence 'steps))))]
    {:name 'ahof-o19/momentum-recurrence :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/app
       (function/const* 'optimization/momentum-iterate-zero [])
       beta rate gradient initial)
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'optimization/momentum-iterate-successor [])
        beta rate gradient 'steps initial)))}))

(def momentum-spec
  (let [velocity-law (:type first-velocity-spec)
        position-law (:type first-position-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o19/momentum :universes []
     :type (proposition/conjunction
            velocity-law (proposition/conjunction position-law recurrence))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      velocity-law (proposition/conjunction position-law recurrence)
      (function/const* 'ahof-o19/first-velocity-is-one [])
      (function/app
       (function/const* 'proposition/conjoin [])
       position-law recurrence
       (function/const* 'ahof-o19/first-position-is-one [])
       (function/const* 'ahof-o19/momentum-recurrence [])))}))

(def theorem-specs
  [first-velocity-spec first-position-spec recurrence-spec momentum-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF momentum expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-o19-momentum}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF momentum declaration rejected"
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
