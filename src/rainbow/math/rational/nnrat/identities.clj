(ns rainbow.math.rational.nnrat.identities
  "Neutral and absorbing laws for native nonnegative rationals, up to cross-product equivalence."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- succ [value] (function/app successor value))
(defn- add-nat [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- denominator-predecessor [value]
  (function/app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- denominator-combine [left right]
  (function/app
   (function/const* 'nnrat/combine-denominator-predecessors [])
   left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- reciprocal [value]
  (function/app (function/const* 'nnrat/reciprocal []) value))
(defn- divide [left right]
  (function/app (function/const* 'nnrat/divide []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat value))
(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))
(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))
(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(defn- denominator-with-right-one [value]
  (let [predecessor (denominator-predecessor value)
        combined (succ (denominator-combine predecessor zero))
        product (multiply-nat (succ predecessor) one)
        target (denominator value)]
    (transitive
     combined product target
     (function/app (function/const* 'nnrat/denominator-combine [])
                   predecessor zero)
     (function/app (function/const* 'nat/multiply-one-right [])
                   (succ predecessor)))))

(defn- denominator-with-left-one [value]
  (let [predecessor (denominator-predecessor value)
        combined (succ (denominator-combine zero predecessor))
        product (multiply-nat one (succ predecessor))
        target (denominator value)]
    (transitive
     combined product target
     (function/app (function/const* 'nnrat/denominator-combine [])
                   zero predecessor)
     (function/app (function/const* 'nat/one-times [])
                   (succ predecessor)))))

(defn- zero-times [value]
  (transitive
   (multiply-nat zero value) (multiply-nat value zero) zero
   (function/app (function/const* 'nat/multiply-commutative []) zero value)
   (function/app (function/const* 'nat/times-zero []) value)))

(def add-zero-right-spec
  {:name 'nnrat/add-zero-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (add 'value nnrat-zero) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          result (add 'value nnrat-zero)
          result-numerator (numerator result)
          result-denominator (denominator result)
          numerator-with-zero (add-nat (multiply-nat n one) zero)
          numerator-to-product
          (function/app (function/const* 'algebra/nat-add-zero-right [])
                        (multiply-nat n one))
          product-to-n
          (function/app (function/const* 'nat/multiply-one-right []) n)
          numerator-same
          (transitive numerator-with-zero (multiply-nat n one) n
                      numerator-to-product product-to-n)
          denominator-same
          (denominator-with-right-one 'value)
          start (multiply-nat result-numerator d)
          middle (multiply-nat n d)
          finish (multiply-nat n result-denominator)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate d))
                     result-numerator n numerator-same)
          replace-denominator
          (symmetric
           finish middle
           (congruent (function/lam [['candidate nat]]
                                    (multiply-nat n 'candidate))
                      result-denominator d denominator-same))]
      (transitive start middle finish
                  replace-numerator replace-denominator)))})

(def add-zero-left-spec
  {:name 'nnrat/add-zero-left
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (add nnrat-zero 'value) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          result (add nnrat-zero 'value)
          result-numerator (numerator result)
          result-denominator (denominator result)
          n-times-one (multiply-nat n one)
          numerator-with-zero (add-nat (multiply-nat zero d) n-times-one)
          replace-zero-product
          (congruent (function/lam [['candidate nat]]
                                   (add-nat 'candidate n-times-one))
                     (multiply-nat zero d) zero (zero-times d))
          remove-zero
          (reflexive n-times-one)
          remove-one
          (function/app (function/const* 'nat/multiply-one-right []) n)
          numerator-same
          (transitive
           numerator-with-zero (add-nat zero n-times-one) n
           replace-zero-product
           (transitive (add-nat zero n-times-one) n-times-one n
                       remove-zero remove-one))
          denominator-same (denominator-with-left-one 'value)
          start (multiply-nat result-numerator d)
          middle (multiply-nat n d)
          finish (multiply-nat n result-denominator)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate d))
                     result-numerator n numerator-same)
          replace-denominator
          (symmetric
           finish middle
           (congruent (function/lam [['candidate nat]]
                                    (multiply-nat n 'candidate))
                      result-denominator d denominator-same))]
      (transitive start middle finish
                  replace-numerator replace-denominator)))})

(def multiply-one-right-spec
  {:name 'nnrat/multiply-one-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (multiply 'value nnrat-one) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          result (multiply 'value nnrat-one)
          result-numerator (numerator result)
          result-denominator (denominator result)
          numerator-same
          (function/app (function/const* 'nat/multiply-one-right []) n)
          denominator-same (denominator-with-right-one 'value)
          start (multiply-nat result-numerator d)
          middle (multiply-nat n d)
          finish (multiply-nat n result-denominator)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate d))
                     result-numerator n numerator-same)
          replace-denominator
          (symmetric
           finish middle
           (congruent (function/lam [['candidate nat]]
                                    (multiply-nat n 'candidate))
                      result-denominator d denominator-same))]
      (transitive start middle finish
                  replace-numerator replace-denominator)))})

(def multiply-one-left-spec
  {:name 'nnrat/multiply-one-left
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (multiply nnrat-one 'value) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          d (denominator 'value)
          result (multiply nnrat-one 'value)
          result-numerator (numerator result)
          result-denominator (denominator result)
          numerator-same
          (function/app (function/const* 'nat/one-times []) n)
          denominator-same (denominator-with-left-one 'value)
          start (multiply-nat result-numerator d)
          middle (multiply-nat n d)
          finish (multiply-nat n result-denominator)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate d))
                     result-numerator n numerator-same)
          replace-denominator
          (symmetric
           finish middle
           (congruent (function/lam [['candidate nat]]
                                    (multiply-nat n 'candidate))
                      result-denominator d denominator-same))]
      (transitive start middle finish
                  replace-numerator replace-denominator)))})

(def multiply-zero-right-spec
  {:name 'nnrat/multiply-zero-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (multiply 'value nnrat-zero) nnrat-zero))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          result (multiply 'value nnrat-zero)
          result-numerator (numerator result)
          start (multiply-nat result-numerator one)
          finish zero
          numerator-zero
          (function/app (function/const* 'nat/times-zero []) n)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate one))
                     result-numerator zero numerator-zero)]
      (transitive start zero finish replace-numerator (reflexive zero))))})

(def multiply-zero-left-spec
  {:name 'nnrat/multiply-zero-left
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (multiply nnrat-zero 'value) nnrat-zero))
   :value
   (function/lam
    [['value nnrat]]
    (let [n (numerator 'value)
          result (multiply nnrat-zero 'value)
          result-numerator (numerator result)
          start (multiply-nat result-numerator one)
          finish zero
          numerator-zero (zero-times n)
          replace-numerator
          (congruent (function/lam [['candidate nat]]
                                   (multiply-nat 'candidate one))
                     result-numerator zero numerator-zero)]
      (transitive start zero finish replace-numerator (reflexive zero))))})

(def reciprocal-one-spec
  {:name 'nnrat/reciprocal-one
   :universes []
   :type (equivalent (reciprocal nnrat-one) nnrat-one)
   :value
   (function/app (function/const* 'nnrat/equivalent-reflexive [])
                 nnrat-one)})

(def divide-one-right-spec
  {:name 'nnrat/divide-one-right
   :universes []
   :type
   (function/forall [['value nnrat]]
                    (equivalent (divide 'value nnrat-one) 'value))
   :value
   (function/lam
    [['value nnrat]]
    (function/app (function/const* 'nnrat/multiply-one-right []) 'value))})

(def theorem-specs
  [add-zero-right-spec add-zero-left-spec
   multiply-one-right-spec multiply-one-left-spec
   multiply-zero-right-spec multiply-zero-left-spec
   reciprocal-one-spec divide-one-right-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nonnegative-rational identity expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :nnrat-identities}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nonnegative-rational identity declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce (fn [env spec] (if (environment/resolve-id env (:name spec)) (support/add-spec-shared env :nnrat-identities spec) (add-spec env spec))) checked-environment theorem-specs))

(defn extend-environment
  "Shared-world safe: an alias already present (nnrat/multiply-one-left is
  also installed by nnrat-distributive) is compared by elaborated type via
  support/add-spec-shared -- identical skips, a different statement throws." [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.identities))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
