(ns rainbow.math.rational.signed.stl
  "Signed minimum and maximum for signal temporal logic (STL) robustness. The
  robustness of an STL formula is computed by structural recursion: an atomic
  predicate contributes a signed margin, conjunction takes the minimum of its
  parts, disjunction the maximum, and negation the sign flip. Minimum and maximum
  are selected by the signed comparison decision on cross products, so a worked
  robustness computation reduces to an exact signed rational."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def bool-false (function/const* 'data/false []))
(def signed (function/const* 'signed/SignedRational []))

(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))
(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- decide-at-most-nat [left right]
  (function/app (function/const* 'nat/decide-at-most []) left right))

(defn- decide [left right]
  (function/app (function/const* 'validation/signed-decide-at-most [])
                left right))

;; A self-contained documentation proposition for the if-data condition slot
;; (if-data ignores it during reduction).
(defn- condition [left right]
  (function/equality type-level bool (decide left right) (decide left right)))

(defn- if-signed [condition decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                signed condition decision then-value else-value))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Definitions --------------------------------------------------------------

(def decide-at-most-spec
  {:name 'validation/signed-decide-at-most :kind :definition :universes []
   :type (function/arrow signed signed bool)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [l (nnrat-add (signed-positive 'left) (signed-negative 'right))
          r (nnrat-add (signed-positive 'right) (signed-negative 'left))]
      (decide-at-most-nat
       (multiply-nat (numerator l) (denominator r))
       (multiply-nat (numerator r) (denominator l)))))})

(def min-spec
  {:name 'validation/signed-min :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (if-signed (condition 'left 'right) (decide 'left 'right)
               'left 'right))})

(def max-spec
  {:name 'validation/signed-max :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (if-signed (condition 'left 'right) (decide 'left 'right)
               'right 'left))})

(def definition-specs [decide-at-most-spec min-spec max-spec])

;; Theorems -----------------------------------------------------------------

(defn- min-term [left right]
  (function/app (function/const* 'validation/signed-min []) left right))
(defn- max-term [left right]
  (function/app (function/const* 'validation/signed-max []) left right))

;; When the decision is false (left not <= right), min selects the right value.
(def min-preserved-spec
  {:name 'validation/signed-min-preserved :universes []
   :type (function/forall
          [['left signed] ['right signed]
           ['not-below (equality bool (decide 'left 'right) bool-false)]]
          (equality signed (min-term 'left 'right) 'right))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['not-below (equality bool (decide 'left 'right) bool-false)]]
    (function/app
     (function/const* 'equality/reverse-substitution [type-level])
     bool (decide 'left 'right) bool-false 'not-below
     (function/lam
      [['d bool]]
      (equality signed
                (if-signed (condition 'left 'right) 'd 'left 'right)
                'right))
     (function/app (function/const* 'equality/reflexive [type-level])
                   signed 'right)))})

;; When the decision is false, max selects the left value.
(def max-preserved-spec
  {:name 'validation/signed-max-preserved :universes []
   :type (function/forall
          [['left signed] ['right signed]
           ['not-below (equality bool (decide 'left 'right) bool-false)]]
          (equality signed (max-term 'left 'right) 'left))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['not-below (equality bool (decide 'left 'right) bool-false)]]
    (function/app
     (function/const* 'equality/reverse-substitution [type-level])
     bool (decide 'left 'right) bool-false 'not-below
     (function/lam
      [['d bool]]
      (equality signed
                (if-signed (condition 'left 'right) 'd 'right 'left)
                'left))
     (function/app (function/const* 'equality/reflexive [type-level])
                   signed 'left)))})

(def theorem-specs [min-preserved-spec max-preserved-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Signed-STL expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :signed-stl}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Signed-STL declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.rational.signed.stl))
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
