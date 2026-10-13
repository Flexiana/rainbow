(ns rainbow.algorithms.proofs.ahof.failure-probability-monitor
  "AHoF V64 worked failure-probability monitor over exact rationals with risk
  threshold 1/2. A failure-probability estimate of 1/4 stays at or below the
  threshold, so the system is safe and no alarm is raised. An estimate of 3/4 exceeds
  the threshold, so the system is unsafe and the alarm trips. Proved native and
  axiom-free.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.failure-probability-monitor`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.failure-probability-monitor :as dep-failure-probability-monitor]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))

(def low-estimate (make-rational (data-nat 1) (data-nat 3)))   ; 1/4
(def high-estimate (make-rational (data-nat 3) (data-nat 3)))  ; 3/4
(def threshold (make-rational (data-nat 1) (data-nat 1)))      ; 1/2

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- safe? [p tau]
  (function/app (function/const* 'failmon/safe? []) p tau))
(defn- alarm? [p tau]
  (function/app (function/const* 'failmon/alarm? []) p tau))

(def tau (function/const* 'ahof-v64/threshold []))

;; Definitions --------------------------------------------------------------

(def threshold-spec
  {:name 'ahof-v64/threshold :kind :definition :universes [] :type nnrat
   :value threshold})

(def definition-specs [threshold-spec])

;; Theorems -----------------------------------------------------------------

;; A failure estimate of 1/4 is at or below the 1/2 threshold: the system is safe.
(def low-is-safe-spec
  {:name 'ahof-v64/low-is-safe :universes []
   :type (equality bool (safe? low-estimate tau) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (safe? low-estimate tau))})

;; ...and no alarm is raised for the safe estimate.
(def low-no-alarm-spec
  {:name 'ahof-v64/low-no-alarm :universes []
   :type (equality bool (alarm? low-estimate tau) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (alarm? low-estimate tau))})

;; A failure estimate of 3/4 exceeds the 1/2 threshold: the system is unsafe.
(def high-is-unsafe-spec
  {:name 'ahof-v64/high-is-unsafe :universes []
   :type (equality bool (safe? high-estimate tau) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (safe? high-estimate tau))})

;; ...and the alarm trips for the unsafe estimate.
(def high-alarms-spec
  {:name 'ahof-v64/high-alarms :universes []
   :type (equality bool (alarm? high-estimate tau) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (alarm? high-estimate tau))})

;; The worked V64 package: a safe estimate raises no alarm and an unsafe estimate
;; trips it.
(def failure-monitor-spec
  (let [safe-law (:type low-no-alarm-spec)
        alarm-law (:type high-alarms-spec)]
    {:name 'ahof-v64/failure-monitor :universes []
     :type (proposition/conjunction safe-law alarm-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      safe-law alarm-law
      (function/const* 'ahof-v64/low-no-alarm [])
      (function/const* 'ahof-v64/high-alarms []))}))

(def theorem-specs
  [low-is-safe-spec low-no-alarm-spec high-is-unsafe-spec high-alarms-spec
   failure-monitor-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF failure-monitor expression failed elaboration"
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
                               :producer :ahof-v64-failure-probability-monitor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF failure-monitor declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.failure-probability-monitor])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.failure-probability-monitor))
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
