(ns rainbow.math.rational.division
  "Exact division of nonnegative rationals. The reciprocal of p/(q+1) is
  (q+1)/p; division is multiplication by the reciprocal. For a positive rational
  (numerator a successor), dividing it by itself is equivalent to one -- the
  cancellation law that underlies Newton steps, secant ratios, and normalization.
  Division by zero is total but junk (the reciprocal of 0 is not a genuine
  inverse), so the cancellation law is stated only for positive numerators."
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
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- predecessor [value]
  (function/app (function/const* 'nat/predecessor []) value))
(defn- make [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(def nat-zero (function/const* 'data/zero []))
(def nat-one (succ nat-zero))
(defn- nat-multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- nat-multiply-commutative [left right]
  (function/app (function/const* 'nat/multiply-commutative []) left right))
(defn- nat-multiply-one-right [value]
  (function/app (function/const* 'nat/multiply-one-right []) value))
(defn- nat-one-times [value]
  (function/app (function/const* 'nat/one-times []) value))
(defn- nat-transitive [left middle right proof-lm proof-mr]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right proof-lm proof-mr))
(defn- nat-symmetric [left right proof]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right proof))

(defn- reciprocal [value]
  (function/app (function/const* 'nnrat/reciprocal []) value))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Definitions --------------------------------------------------------------

(def reciprocal-spec
  {:name 'nnrat/reciprocal :kind :definition :universes []
   :type (function/arrow nnrat nnrat)
   :value (function/lam [['value nnrat]]
                        (make (denominator 'value)
                              (predecessor (numerator 'value))))})

(def divide-spec
  {:name 'nnrat/divide :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['left nnrat] ['right nnrat]]
                        (nnrat-multiply 'left (reciprocal 'right)))})

(def definition-specs [reciprocal-spec divide-spec])

;; Theorems -----------------------------------------------------------------

(def reciprocal-unfold-spec
  {:name 'nnrat/reciprocal-unfold :universes []
   :type (function/forall
          [['value nnrat]]
          (equality nnrat (reciprocal 'value)
                    (make (denominator 'value)
                          (predecessor (numerator 'value)))))
   :value (function/lam [['value nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (reciprocal 'value)))})

(def divide-unfold-spec
  {:name 'nnrat/divide-unfold :universes []
   :type (function/forall
          [['left nnrat] ['right nnrat]]
          (equality nnrat (divide 'left 'right)
                    (nnrat-multiply 'left (reciprocal 'right))))
   :value (function/lam [['left nnrat] ['right nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (divide 'left 'right)))})

;; For any positive rational (succ p)/(q+1), dividing it by itself is
;; equivalent to one. The equivalence cross-product reduces to
;; ((succ p)(succ q)) * 1 = 1 * ((succ q)(succ p)); the chain bridges the
;; multiply-by-one wrappers around nat multiply commutativity.
(def divide-self-positive-spec
  (let [x (nat-multiply (succ 'p) (succ 'q))
        y (nat-multiply (succ 'q) (succ 'p))]
    {:name 'nnrat/divide-self-positive :universes []
     :type (function/forall
            [['p nat] ['q nat]]
            (nnrat-equivalent (divide (make (succ 'p) 'q) (make (succ 'p) 'q))
                              nnrat-one))
     :value (function/lam [['p nat] ['q nat]]
                          (nat-transitive
                           (nat-multiply x nat-one) y (nat-multiply nat-one y)
                           (nat-transitive
                            (nat-multiply x nat-one) x y
                            (nat-multiply-one-right x)
                            (nat-multiply-commutative (succ 'p) (succ 'q)))
                           (nat-symmetric (nat-multiply nat-one y) y
                                          (nat-one-times y))))}))

(def theorem-specs
  [reciprocal-unfold-spec divide-unfold-spec divide-self-positive-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Rational-division expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :rational-division}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Rational-division declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.rational.division))
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
