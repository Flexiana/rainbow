(ns rainbow.algorithms.proofs.failure-probability-monitor
  "Runtime failure-probability monitoring over exact rationals (AHoF V64). An online
  estimator maintains a failure-probability estimate p; the monitor declares the
  system SAFE while p stays at or below a risk threshold tau, and raises an ALARM
  exactly when it does not:

      safe?  p tau = decide (p <= tau)
      alarm? p tau = NOT (safe? p tau)      (boolean negation via logic/if-data)

  over exact rationals. The alarm is the boolean complement of the safety test, so
  every observation either keeps the system safe or trips the alarm. Proved native
  and axiom-free: the safety decision and the alarm as its negation, each with an
  unfold theorem. The online importance-sampling update of p is executable; what is
  proved is the threshold decision and its complement.

  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.failure-probability-monitor`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- safe? [p tau]
  (function/app (function/const* 'failmon/safe? []) p tau))

;; boolean NOT: if x then false else true
(defn- not-bool [x]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition x) x false-value true-value))

;; Definitions --------------------------------------------------------------

;; safe? p tau = decide (p <= tau)
(def safe-spec
  {:name 'failmon/safe? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['p nnrat] ['tau nnrat]] (decide-at-most 'p 'tau))})

;; alarm? p tau = NOT (safe? p tau)
(def alarm-spec
  {:name 'failmon/alarm? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['p nnrat] ['tau nnrat]] (not-bool (safe? 'p 'tau)))})

(def definition-specs [safe-spec alarm-spec])

;; Theorems -----------------------------------------------------------------

(def safe-unfold-spec
  {:name 'failmon/safe-unfold :universes []
   :type (function/forall [['p nnrat] ['tau nnrat]]
                          (equality bool (safe? 'p 'tau)
                                    (decide-at-most 'p 'tau)))
   :value (function/lam [['p nnrat] ['tau nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (safe? 'p 'tau)))})

(def alarm-unfold-spec
  {:name 'failmon/alarm-unfold :universes []
   :type (function/forall [['p nnrat] ['tau nnrat]]
                          (equality bool
                                    (function/app
                                     (function/const* 'failmon/alarm? []) 'p 'tau)
                                    (not-bool (safe? 'p 'tau))))
   :value (function/lam [['p nnrat] ['tau nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (function/app
                               (function/const* 'failmon/alarm? []) 'p 'tau)))})

(def theorem-specs [safe-unfold-spec alarm-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Failure-probability-monitor expression failed elaboration"
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
                               :producer :failure-probability-monitor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Failure-probability-monitor declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.failure-probability-monitor))
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
