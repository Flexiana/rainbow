(ns rainbow.algorithms.proofs.ahof.stl-robustness
  "AHoF V6 worked signal-temporal-logic robustness over signed rationals.

  Two atomic robustness margins x = 1/2 (satisfied) and y = -1/4 (violated) are
  combined by the STL connectives: conjunction robustness is their minimum
  (-1/4, so the conjunction is violated), disjunction robustness is their maximum
  (1/2, satisfied), and negation flips the sign of x (-1/2). The conjunction's
  minimum is selected through the checked signed-min engine.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.stl-robustness`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.rational.signed.stl :as dep-signed-stl]
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
(def bool-false (function/const* 'data/false []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
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
(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(def one-half (make-rational (data-nat 1) (data-nat 1)))
(def one-quarter (make-rational (data-nat 1) (data-nat 3)))

(def x (function/const* 'ahof-v6/signal-x []))
(def y (function/const* 'ahof-v6/signal-y []))

(defn- decide [left right]
  (function/app (function/const* 'validation/signed-decide-at-most [])
                left right))
(defn- signed-min [left right]
  (function/app (function/const* 'validation/signed-min []) left right))
(defn- signed-max [left right]
  (function/app (function/const* 'validation/signed-max []) left right))

;; Definitions --------------------------------------------------------------

(def signal-x-spec
  {:name 'ahof-v6/signal-x :kind :definition :universes []
   :type signed :value (from-nnrat one-half)})            ; +1/2

(def signal-y-spec
  {:name 'ahof-v6/signal-y :kind :definition :universes []
   :type signed :value (signed-make nnrat-zero one-quarter)})  ; -1/4

(def and-robustness-spec
  {:name 'ahof-v6/and-robustness :kind :definition :universes []
   :type signed :value (signed-min x y)})

(def or-robustness-spec
  {:name 'ahof-v6/or-robustness :kind :definition :universes []
   :type signed :value (signed-max x y)})

(def not-robustness-spec
  {:name 'ahof-v6/not-robustness :kind :definition :universes []
   :type signed :value (signed-negate x)})

(def definition-specs
  [signal-x-spec signal-y-spec and-robustness-spec or-robustness-spec
   not-robustness-spec])

;; Theorems -----------------------------------------------------------------

;; The conjunction selects the smaller (violated) margin via the signed-min
;; engine: since x is not <= y, the minimum is y.
(def and-selects-minimum-spec
  {:name 'ahof-v6/and-selects-minimum :universes []
   :type (equality signed (signed-min x y) y)
   :value (function/app
           (function/const* 'validation/signed-min-preserved [])
           x y
           (function/app (function/const* 'equality/reflexive [type-level])
                         bool bool-false))})

(def robustness-values-spec
  (let [three (data-nat 3)
        minus-quarter (signed-make nnrat-zero one-quarter)   ; -1/4
        half (from-nnrat one-half)                            ; +1/2
        minus-half (signed-make nnrat-zero one-half)          ; -1/2
        eq-and (signed-equivalent (function/const* 'ahof-v6/and-robustness [])
                                  minus-quarter)
        eq-or (signed-equivalent (function/const* 'ahof-v6/or-robustness [])
                                 half)
        eq-not (signed-equivalent (function/const* 'ahof-v6/not-robustness [])
                                  minus-half)]
    {:name 'ahof-v6/robustness-values :universes []
     :type (proposition/conjunction
            eq-and (proposition/conjunction eq-or eq-not))
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      eq-and (proposition/conjunction eq-or eq-not)
      (signed-equivalent-cross (function/const* 'ahof-v6/and-robustness [])
                               minus-quarter)
      (function/app
       (function/const* 'proposition/conjoin [])
       eq-or eq-not
       (signed-equivalent-cross (function/const* 'ahof-v6/or-robustness [])
                                half)
       (signed-equivalent-cross (function/const* 'ahof-v6/not-robustness [])
                                minus-half)))}))

(def stl-robustness-spec
  (let [selects (:type and-selects-minimum-spec)
        values (:type robustness-values-spec)]
    {:name 'ahof-v6/stl-robustness :universes []
     :type (proposition/conjunction selects values)
     :value (function/app
             (function/const* 'proposition/conjoin [])
             selects values
             (function/const* 'ahof-v6/and-selects-minimum [])
             (function/const* 'ahof-v6/robustness-values []))}))

(def theorem-specs
  [and-selects-minimum-spec robustness-values-spec stl-robustness-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF STL expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :ahof-v6-stl-robustness}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF STL declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.stl])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.stl-robustness))
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
