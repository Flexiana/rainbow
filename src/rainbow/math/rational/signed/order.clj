(ns rainbow.math.rational.signed.order
  "Order and structural laws for signed rationals. The signed order a <= b is
  the additive comparison pos(a) + neg(b) <= pos(b) + neg(a), reusing the
  nonnegative-rational order without any primitive subtraction. This is the
  foundation for signed minima and maxima (e.g. STL robustness) and for
  monotonicity results over descent and learning trajectories."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

;; Definitions --------------------------------------------------------------

(def at-most-spec
  {:name 'signed/at-most :kind :definition :universes []
   :type (function/arrow signed signed 'Prop)
   :value (function/lam
           [['left signed] ['right signed]]
           (nnrat-at-most
            (nnrat-add (signed-positive 'left) (signed-negative 'right))
            (nnrat-add (signed-positive 'right) (signed-negative 'left))))})

(def definition-specs [at-most-spec])

;; Theorems -----------------------------------------------------------------

(def at-most-reflexive-spec
  {:name 'signed/at-most-reflexive :universes []
   :type (function/forall [['value signed]]
                          (function/app (function/const* 'signed/at-most [])
                                        'value 'value))
   :value (function/lam
           [['value signed]]
           (function/app
            (function/const* 'nnrat/at-most-reflexive [])
            (nnrat-add (signed-positive 'value) (signed-negative 'value))))})

;; The signed negation is involutive up to signed equivalence: - - a ~ a.
(def negate-involutive-spec
  {:name 'signed/negate-involutive :universes []
   :type (function/forall [['value signed]]
                          (signed-equivalent (signed-negate (signed-negate 'value))
                                             'value))
   :value (function/lam
           [['value signed]]
           (function/app
            (function/const* 'nnrat/equivalent-reflexive [])
            (nnrat-add (signed-positive (signed-negate (signed-negate 'value)))
                       (signed-negative 'value))))})

(def theorem-specs [at-most-reflexive-spec negate-involutive-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Signed-order expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :signed-order}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Signed-order declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.rational.signed.order))
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
