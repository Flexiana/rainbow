(ns rainbow.algorithms.proofs.ahof.interval-arithmetic
  "AHoF V40 worked interval arithmetic over exact rationals on the interval
  [1/2, 3/2]. The midpoint 1 lies inside (1/2 <= 1 <= 3/2); 1/4 lies below the lower
  endpoint and 2 lies above the upper endpoint, so both are outside. Interval
  addition [1/2,3/2] + [1/2,3/2] = [1, 3] has lower endpoint 1/2 + 1/2 = 1 and upper
  endpoint 3/2 + 3/2 = 3, each proved by cross-product equivalence (the sums land on
  non-canonical make-pairs, so nnrat/equivalent is used rather than reflexivity).
  Proved native and axiom-free.

  Scope (measured by the kernel): this module has 6 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.interval-arithmetic`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.interval-membership :as dep-interval-membership]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))

(def lo-value (make-rational (data-nat 1) (data-nat 1)))    ; 1/2
(def hi-value (make-rational (data-nat 3) (data-nat 1)))    ; 3/2
(def whole-1 (make-rational (data-nat 1) (data-nat 0)))     ; 1
(def whole-2 (make-rational (data-nat 2) (data-nat 0)))     ; 2
(def whole-3 (make-rational (data-nat 3) (data-nat 0)))     ; 3
(def quarter (make-rational (data-nat 1) (data-nat 3)))     ; 1/4

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-cross [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- interval-contains? [lo hi x]
  (function/app (function/const* 'validation/interval-contains? []) lo hi x))
(defn- interval-add-endpoint [p q]
  (function/app (function/const* 'validation/interval-add-endpoint []) p q))

(def lo (function/const* 'ahof-v40/lo []))
(def hi (function/const* 'ahof-v40/hi []))

;; Definitions --------------------------------------------------------------

(def lo-spec
  {:name 'ahof-v40/lo :kind :definition :universes [] :type nnrat
   :value lo-value})
(def hi-spec
  {:name 'ahof-v40/hi :kind :definition :universes [] :type nnrat
   :value hi-value})
(def sum-lo-endpoint-spec
  {:name 'ahof-v40/sum-lo-endpoint :kind :definition :universes [] :type nnrat
   :value (interval-add-endpoint lo lo)})
(def sum-hi-endpoint-spec
  {:name 'ahof-v40/sum-hi-endpoint :kind :definition :universes [] :type nnrat
   :value (interval-add-endpoint hi hi)})

(def definition-specs
  [lo-spec hi-spec sum-lo-endpoint-spec sum-hi-endpoint-spec])

;; Theorems -----------------------------------------------------------------

;; The midpoint 1 lies inside [1/2, 3/2].
(def midpoint-inside-spec
  {:name 'ahof-v40/midpoint-inside :universes []
   :type (equality bool (interval-contains? lo hi whole-1) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (interval-contains? lo hi whole-1))})

;; 1/4 lies below the lower endpoint, so it is outside.
(def below-outside-spec
  {:name 'ahof-v40/below-outside :universes []
   :type (equality bool (interval-contains? lo hi quarter) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (interval-contains? lo hi quarter))})

;; 2 lies above the upper endpoint, so it is outside.
(def above-outside-spec
  {:name 'ahof-v40/above-outside :universes []
   :type (equality bool (interval-contains? lo hi whole-2) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (interval-contains? lo hi whole-2))})

;; Lower endpoint of the interval sum: 1/2 + 1/2 = 1.
(def sum-lo-spec
  {:name 'ahof-v40/sum-lo :universes []
   :type (nnrat-equivalent (function/const* 'ahof-v40/sum-lo-endpoint []) whole-1)
   :value (equivalent-cross (function/const* 'ahof-v40/sum-lo-endpoint []) whole-1)})

;; Upper endpoint of the interval sum: 3/2 + 3/2 = 3.
(def sum-hi-spec
  {:name 'ahof-v40/sum-hi :universes []
   :type (nnrat-equivalent (function/const* 'ahof-v40/sum-hi-endpoint []) whole-3)
   :value (equivalent-cross (function/const* 'ahof-v40/sum-hi-endpoint []) whole-3)})

;; The worked V40 package: the midpoint is inside and a below-point is outside.
(def interval-arithmetic-spec
  (let [inside-law (:type midpoint-inside-spec)
        outside-law (:type below-outside-spec)]
    {:name 'ahof-v40/interval-arithmetic :universes []
     :type (proposition/conjunction inside-law outside-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      inside-law outside-law
      (function/const* 'ahof-v40/midpoint-inside [])
      (function/const* 'ahof-v40/below-outside []))}))

(def theorem-specs
  [midpoint-inside-spec below-outside-spec above-outside-spec
   sum-lo-spec sum-hi-spec interval-arithmetic-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF interval-arithmetic expression failed elaboration"
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
          :rainbow/provenance {:origin :native
                               :producer :ahof-v40-interval-arithmetic}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF interval-arithmetic declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.interval-membership])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.interval-arithmetic))
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
