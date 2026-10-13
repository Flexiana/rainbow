(ns rainbow.algorithms.proofs.ahof.odd-monitor
  "AHoF V59 worked ODD monitor over the 2-D operating envelope [0,1] x [0,2]. The
  operating point (1/2, 1) lies inside the box, so the monitor accepts it. The point
  (1/2, 3) violates the second-dimension upper bound (3 > 2) and the point (2, 1)
  violates the first-dimension upper bound (2 > 1); either single violation drives
  the point outside the ODD, so the monitor rejects both -- the runtime alarm
  condition. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.odd-monitor`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.odd-monitor :as dep-odd-monitor]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def bool (function/const* 'data/Bool []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))

(def whole-0 (make-rational (data-nat 0) (data-nat 0)))    ; 0
(def whole-1 (make-rational (data-nat 1) (data-nat 0)))    ; 1
(def whole-2 (make-rational (data-nat 2) (data-nat 0)))    ; 2
(def whole-3 (make-rational (data-nat 3) (data-nat 0)))    ; 3
(def half (make-rational (data-nat 1) (data-nat 1)))       ; 1/2

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- in-odd? [lo1 hi1 x1 lo2 hi2 x2]
  (function/app (function/const* 'monitor/in-odd? []) lo1 hi1 x1 lo2 hi2 x2))

(def lo1 (function/const* 'ahof-v59/lo1 []))
(def hi1 (function/const* 'ahof-v59/hi1 []))
(def lo2 (function/const* 'ahof-v59/lo2 []))
(def hi2 (function/const* 'ahof-v59/hi2 []))

;; Definitions --------------------------------------------------------------

(def lo1-spec {:name 'ahof-v59/lo1 :kind :definition :universes [] :type nnrat
               :value whole-0})
(def hi1-spec {:name 'ahof-v59/hi1 :kind :definition :universes [] :type nnrat
               :value whole-1})
(def lo2-spec {:name 'ahof-v59/lo2 :kind :definition :universes [] :type nnrat
               :value whole-0})
(def hi2-spec {:name 'ahof-v59/hi2 :kind :definition :universes [] :type nnrat
               :value whole-2})

(def definition-specs [lo1-spec hi1-spec lo2-spec hi2-spec])

;; Theorems -----------------------------------------------------------------

;; (1/2, 1) is inside [0,1] x [0,2]: the monitor accepts.
(def inside-accepted-spec
  {:name 'ahof-v59/inside-accepted :universes []
   :type (equality bool (in-odd? lo1 hi1 half lo2 hi2 whole-1) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-odd? lo1 hi1 half lo2 hi2 whole-1))})

;; (1/2, 3) violates the second-dimension upper bound: the monitor rejects.
(def dim2-above-rejected-spec
  {:name 'ahof-v59/dim2-above-rejected :universes []
   :type (equality bool (in-odd? lo1 hi1 half lo2 hi2 whole-3) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-odd? lo1 hi1 half lo2 hi2 whole-3))})

;; (2, 1) violates the first-dimension upper bound: the monitor rejects.
(def dim1-above-rejected-spec
  {:name 'ahof-v59/dim1-above-rejected :universes []
   :type (equality bool (in-odd? lo1 hi1 whole-2 lo2 hi2 whole-1) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-odd? lo1 hi1 whole-2 lo2 hi2 whole-1))})

;; The worked V59 package: the inside point is accepted and a boundary-violating
;; point is rejected.
(def odd-monitor-spec
  (let [accept-law (:type inside-accepted-spec)
        reject-law (:type dim2-above-rejected-spec)]
    {:name 'ahof-v59/odd-monitor :universes []
     :type (proposition/conjunction accept-law reject-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      accept-law reject-law
      (function/const* 'ahof-v59/inside-accepted [])
      (function/const* 'ahof-v59/dim2-above-rejected []))}))

(def theorem-specs
  [inside-accepted-spec dim2-above-rejected-spec dim1-above-rejected-spec
   odd-monitor-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF ODD-monitor expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-v59-odd-monitor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF ODD-monitor declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.odd-monitor])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.odd-monitor))
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
