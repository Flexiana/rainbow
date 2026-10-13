(ns rainbow.algorithms.proofs.ahof.gradient-ascent
  "AHoF D49 worked bounded fixed-rate gradient-ascent instance.

  A constant unit gradient with rate 1/2 from the origin produces the exact
  rational trajectory 1/2, 1, 3/2 over three steps. The schedule-prefix
  recurrence reuses the generic gradient-ascent engine; the worked values are
  exact-rational equivalences proved by cross-product reflexivity.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gradient-ascent`
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
(def nnrat-half (function/const* 'nnrat/half []))

(defn- succ-data [value]
  (function/app (function/const* 'data/succ []) value))

(defn- data-nat [n]
  (nth (iterate succ-data (function/const* 'data/zero [])) n))

(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make [])
                numerator denominator-predecessor))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; A cross-product reflexivity proof of (equivalent left right), valid whenever
;; the two rationals reduce to equal cross products.
(defn- equivalent-by-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

(def gradient (function/const* 'ahof-d49/gradient []))
(def rate (function/const* 'ahof-d49/rate []))
(def initial (function/const* 'ahof-d49/initial []))

(defn- ascent-step [point]
  (function/app (function/const* 'optimization/nnrat-ascent-step [])
                gradient rate point))

(defn- ascent-iterate [steps start]
  (function/app (function/const* 'optimization/nnrat-ascent-iterate [])
                gradient rate steps start))

;; Definitions --------------------------------------------------------------

(def gradient-spec
  {:name 'ahof-d49/gradient :kind :definition :universes []
   :type (function/arrow nnrat nnrat)
   :value (function/lam [['ignored-point nnrat]] nnrat-one)})

(def rate-spec
  {:name 'ahof-d49/rate :kind :definition :universes []
   :type nnrat :value nnrat-half})

(def initial-spec
  {:name 'ahof-d49/initial :kind :definition :universes []
   :type nnrat :value nnrat-zero})

(def trajectory-spec
  {:name 'ahof-d49/trajectory :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['steps nat]] (ascent-iterate 'steps initial))})

(def definition-specs
  [gradient-spec rate-spec initial-spec trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def recurrence-spec
  (let [sequence (fn [steps] (ascent-iterate steps initial))
        step
        (function/lam
         [['step-index nat] ['previous nnrat]]
         (ascent-step 'previous))
        base-law
        (equality nnrat (sequence (function/const* 'data/zero [])) initial)
        successor-law
        (function/forall
         [['steps nat]]
         (equality nnrat (sequence (succ-data 'steps))
                   (function/app step 'steps (sequence 'steps))))]
    {:name 'ahof-d49/gradient-ascent-recurrence :universes []
     :type (proposition/conjunction base-law successor-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law successor-law
      (function/app
       (function/const* 'optimization/nnrat-ascent-iterate-zero [])
       gradient rate initial)
      (function/lam
       [['steps nat]]
       (function/app
        (function/const* 'optimization/nnrat-ascent-iterate-successor [])
        gradient rate 'steps initial)))}))

(def worked-trajectory-spec
  (let [t1 (ascent-iterate (data-nat 1) initial)
        t2 (ascent-iterate (data-nat 2) initial)
        t3 (ascent-iterate (data-nat 3) initial)
        three-halves (make-rational (data-nat 3) (data-nat 1))
        at-1 (equivalent t1 nnrat-half)
        at-2 (equivalent t2 nnrat-one)
        at-3 (equivalent t3 three-halves)]
    {:name 'ahof-d49/worked-trajectory :universes []
     :type (proposition/conjunction
            at-1 (proposition/conjunction at-2 at-3))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      at-1 (proposition/conjunction at-2 at-3)
      (equivalent-by-cross t1 nnrat-half)
      (function/app
       (function/const* 'proposition/conjoin [])
       at-2 at-3
       (equivalent-by-cross t2 nnrat-one)
       (equivalent-by-cross t3 three-halves)))}))

(def gradient-ascent-spec
  (let [recurrence (:type recurrence-spec)
        trajectory (:type worked-trajectory-spec)]
    {:name 'ahof-d49/gradient-ascent :universes []
     :type (proposition/conjunction recurrence trajectory)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      recurrence trajectory
      (function/const* 'ahof-d49/gradient-ascent-recurrence [])
      (function/const* 'ahof-d49/worked-trajectory []))}))

(def theorem-specs
  [recurrence-spec worked-trajectory-spec gradient-ascent-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF gradient-ascent expression failed elaboration"
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
          {:origin :native :producer :ahof-d49-gradient-ascent}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF gradient-ascent declaration rejected"
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
