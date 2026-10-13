(ns rainbow.algorithms.proofs.ahof.gradient-descent
  "AHoF O17 worked bounded gradient descent over signed rationals.

  A constant unit gradient with rate 1/2 from the signed point 1 produces the
  exact trajectory 1, 1/2, 0, -1/2: descent drives the parameter through zero
  and into negative values, which only signed rationals can represent. The
  trajectory values are proved by signed cross-product equivalence.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gradient-descent`
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

(defn- succ [value] (function/app (function/const* 'data/succ []) value))

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

;; A proof of signed/equivalent left right via cross-product reflexivity: the
;; relation unfolds to Eq nat over positive+negative cross sums.
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(def rate (function/const* 'ahof-o17/rate []))
(def gradient (function/const* 'ahof-o17/gradient []))
(def initial (function/const* 'ahof-o17/initial []))

(defn- descent-iterate [steps start]
  (function/app (function/const* 'optimization/signed-descent-iterate [])
                rate gradient steps start))

;; Definitions --------------------------------------------------------------

(def rate-spec
  {:name 'ahof-o17/rate :kind :definition :universes []
   :type nnrat :value half})

(def gradient-spec
  {:name 'ahof-o17/gradient :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['ignored-point signed]] nnrat-one)})

(def initial-spec
  {:name 'ahof-o17/initial :kind :definition :universes []
   :type signed :value (from-nnrat nnrat-one)})

(def trajectory-spec
  {:name 'ahof-o17/trajectory :kind :definition :universes []
   :type (function/arrow nat signed)
   :value (function/lam [['steps nat]] (descent-iterate 'steps initial))})

(def definition-specs
  [rate-spec gradient-spec initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def trajectory-values-spec
  (let [x1 (descent-iterate (data-nat 1) initial)
        x2 (descent-iterate (data-nat 2) initial)
        x3 (descent-iterate (data-nat 3) initial)
        at-half (from-nnrat half)
        at-zero (from-nnrat nnrat-zero)
        at-neg-half (signed-make nnrat-zero half)
        eq-1 (signed-equivalent x1 at-half)
        eq-2 (signed-equivalent x2 at-zero)
        eq-3 (signed-equivalent x3 at-neg-half)]
    {:name 'ahof-o17/trajectory-values :universes []
     :type (proposition/conjunction
            eq-1 (proposition/conjunction eq-2 eq-3))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      eq-1 (proposition/conjunction eq-2 eq-3)
      (signed-equivalent-cross x1 at-half)
      (function/app
       (function/const* 'proposition/conjoin [])
       eq-2 eq-3
       (signed-equivalent-cross x2 at-zero)
       (signed-equivalent-cross x3 at-neg-half)))}))

(def recurrence-spec
  (let [sequence (fn [steps] (descent-iterate steps initial))
        step (function/lam
              [['step-index nat] ['previous signed]]
              (function/app (function/const* 'optimization/signed-descent-step [])
                            rate gradient 'previous))
        base-law (equality signed
                           (sequence (function/const* 'data/zero [])) initial)
        successor-law
        (function/forall
         [['steps nat]]
         (equality signed (sequence (succ 'steps))
                   (function/app step 'steps (sequence 'steps))))]
    {:name 'ahof-o17/descent-recurrence :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/app
       (function/const* 'optimization/signed-descent-iterate-zero [])
       rate gradient initial)
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'optimization/signed-descent-iterate-successor [])
        rate gradient 'steps initial)))}))

(def gradient-descent-spec
  (let [values (:type trajectory-values-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o17/gradient-descent :universes []
     :type (proposition/conjunction values recurrence)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      values recurrence
      (function/const* 'ahof-o17/trajectory-values [])
      (function/const* 'ahof-o17/descent-recurrence []))}))

(def theorem-specs
  [trajectory-values-spec recurrence-spec gradient-descent-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF gradient-descent expression failed elaboration"
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
          {:origin :native :producer :ahof-o17-gradient-descent}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF gradient-descent declaration rejected"
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
