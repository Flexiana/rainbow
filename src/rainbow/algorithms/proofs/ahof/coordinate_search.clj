(ns rainbow.algorithms.proofs.ahof.coordinate-search
  "AHoF O32 worked cyclic coordinate search over signed-rational pair state.

  Rate 1 with per-coordinate gradients that read the positive part of each
  coordinate, starting from the point (2, 2). One cycle descends the first
  coordinate to 2 - 1 * 2 = 0, then descends the second coordinate of the updated
  state to 2 - 1 * 2 = 0, reaching (0, 0). The second update reads the state left
  by the first, so the coordinate optimizations compose in turn. The coordinates
  are proved by signed cross-product equivalence.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.coordinate-search`
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

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- state-pair [x y]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x y))
(defn- first-coordinate [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- second-coordinate [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))

(def rate (function/const* 'ahof-o32/rate []))
(def gradient-first (function/const* 'ahof-o32/gradient-first []))
(def gradient-second (function/const* 'ahof-o32/gradient-second []))
(def initial (function/const* 'ahof-o32/initial []))

(defn- coordinate-iterate [steps start]
  (function/app (function/const* 'search/coordinate-iterate [])
                rate gradient-first gradient-second steps start))
(defn- coordinate-cycle [s]
  (function/app (function/const* 'search/coordinate-cycle [])
                rate gradient-first gradient-second s))

;; Definitions --------------------------------------------------------------

(def rate-spec
  {:name 'ahof-o32/rate :kind :definition :universes []
   :type nnrat :value nnrat-one})

;; Partial gradients: the positive part of each coordinate.
(def gradient-first-spec
  {:name 'ahof-o32/gradient-first :kind :definition :universes []
   :type (function/arrow state nnrat)
   :value (function/lam [['s state]] (signed-positive (first-coordinate 's)))})

(def gradient-second-spec
  {:name 'ahof-o32/gradient-second :kind :definition :universes []
   :type (function/arrow state nnrat)
   :value (function/lam [['s state]] (signed-positive (second-coordinate 's)))})

(def initial-spec
  {:name 'ahof-o32/initial :kind :definition :universes []
   :type state
   :value (state-pair (from-nnrat two) (from-nnrat two))})

(def trajectory-spec
  {:name 'ahof-o32/trajectory :kind :definition :universes []
   :type (function/arrow nat state)
   :value (function/lam [['steps nat]] (coordinate-iterate 'steps initial))})

(def definition-specs
  [rate-spec gradient-first-spec gradient-second-spec initial-spec
   trajectory-spec])

;; Theorems -----------------------------------------------------------------

(def first-coordinate-spec
  (let [cycle-one (coordinate-iterate (data-nat 1) initial)
        at-zero (from-nnrat nnrat-zero)]
    {:name 'ahof-o32/first-coordinate-descends-to-zero :universes []
     :type (signed-equivalent (first-coordinate cycle-one) at-zero)
     :value (signed-equivalent-cross (first-coordinate cycle-one) at-zero)}))

(def second-coordinate-spec
  (let [cycle-one (coordinate-iterate (data-nat 1) initial)
        at-zero (from-nnrat nnrat-zero)]
    {:name 'ahof-o32/second-coordinate-descends-to-zero :universes []
     :type (signed-equivalent (second-coordinate cycle-one) at-zero)
     :value (signed-equivalent-cross (second-coordinate cycle-one) at-zero)}))

(def recurrence-spec
  (let [base-law (equality state
                           (coordinate-iterate (function/const* 'data/zero [])
                                               initial)
                           initial)
        cycle-law (equality state
                            (coordinate-iterate (data-nat 1) initial)
                            (coordinate-cycle initial))]
    {:name 'ahof-o32/coordinate-recurrence :universes []
     :type (proposition/conjunction base-law cycle-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      base-law cycle-law
      (function/app
       (function/const* 'search/coordinate-iterate-zero [])
       rate gradient-first gradient-second initial)
      (function/app (function/const* 'equality/reflexive [type-level])
                    state (coordinate-iterate (data-nat 1) initial)))}))

(def coordinate-search-spec
  (let [first-law (:type first-coordinate-spec)
        second-law (:type second-coordinate-spec)
        recurrence (:type recurrence-spec)]
    {:name 'ahof-o32/coordinate-search :universes []
     :type (proposition/conjunction
            first-law (proposition/conjunction second-law recurrence))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      first-law (proposition/conjunction second-law recurrence)
      (function/const* 'ahof-o32/first-coordinate-descends-to-zero [])
      (function/app
       (function/const* 'proposition/conjoin [])
       second-law recurrence
       (function/const* 'ahof-o32/second-coordinate-descends-to-zero [])
       (function/const* 'ahof-o32/coordinate-recurrence [])))}))

(def theorem-specs
  [first-coordinate-spec second-coordinate-spec recurrence-spec
   coordinate-search-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF coordinate-search expression failed elaboration"
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
          {:origin :native :producer :ahof-o32-coordinate-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF coordinate-search declaration rejected"
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
