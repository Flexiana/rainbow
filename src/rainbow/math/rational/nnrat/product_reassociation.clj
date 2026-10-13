(ns rainbow.math.rational.nnrat.product-reassociation
  "Associativity and factor reassociation for native nonnegative rationals."
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

(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))

(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(defn- equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))

(defn- equivalent-symmetric [left right same]
  (function/app (function/const* 'nnrat/equivalent-symmetric [])
                left right same))

(defn- equivalent-reflexive [value]
  (function/app (function/const* 'nnrat/equivalent-reflexive []) value))

(defn- multiply-respects [left left-equivalent right right-equivalent
                          same-left same-right]
  (function/app (function/const* 'nnrat/multiply-respects-equivalence [])
                left left-equivalent right right-equivalent
                same-left same-right))

(def multiply-associative-spec
  {:name 'nnrat/multiply-associative
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (equivalent (multiply (multiply 'a 'b) 'c)
                (multiply 'a (multiply 'b 'c))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (let [na (numerator 'a) nb (numerator 'b) nc (numerator 'c)
          da (denominator 'a) db (denominator 'b) dc (denominator 'c)
          left (multiply (multiply 'a 'b) 'c)
          right (multiply 'a (multiply 'b 'c))
          left-numerator (numerator left)
          right-numerator (numerator right)
          left-denominator (denominator left)
          right-denominator (denominator right)
          numerator-same
          (function/app (function/const* 'nat/multiply-associative [])
                        na nb nc)
          denominator-same
          (function/app (function/const* 'nat/multiply-associative [])
                        da db dc)
          start (multiply-nat left-numerator right-denominator)
          middle (multiply-nat right-numerator right-denominator)
          finish (multiply-nat right-numerator left-denominator)
          replace-numerator
          (congruent
           (function/lam [['candidate nat]]
                         (multiply-nat 'candidate right-denominator))
           left-numerator right-numerator numerator-same)
          replace-denominator
          (congruent
           (function/lam [['candidate nat]]
                         (multiply-nat right-numerator 'candidate))
           right-denominator left-denominator
           (symmetric left-denominator right-denominator denominator-same))]
      (transitive start middle finish
                  replace-numerator replace-denominator)))})

(def multiply-swap-right-spec
  {:name 'nnrat/multiply-swap-right
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (equivalent (multiply (multiply 'a 'b) 'c)
                (multiply (multiply 'a 'c) 'b)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat]]
    (let [start (multiply (multiply 'a 'b) 'c)
          associated (multiply 'a (multiply 'b 'c))
          swapped (multiply 'a (multiply 'c 'b))
          finish (multiply (multiply 'a 'c) 'b)
          associate
          (function/app (function/const* 'nnrat/multiply-associative [])
                        'a 'b 'c)
          commute-inside
          (multiply-respects
           'a 'a (multiply 'b 'c) (multiply 'c 'b)
           (equivalent-reflexive 'a)
           (function/app (function/const* 'nnrat/multiply-commutative [])
                         'b 'c))
          unassociate
          (equivalent-symmetric
           finish swapped
           (function/app (function/const* 'nnrat/multiply-associative [])
                         'a 'c 'b))]
      (equivalent-transitive
       start associated finish associate
       (equivalent-transitive associated swapped finish
                              commute-inside unassociate))))})

(def multiply-four-reorder-spec
  {:name 'nnrat/multiply-four-reorder
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (equivalent
     (multiply (multiply 'a 'b) (multiply 'c 'd))
     (multiply (multiply 'a 'c) (multiply 'b 'd))))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['c nnrat] ['d nnrat]]
    (let [start (multiply (multiply 'a 'b) (multiply 'c 'd))
          first (multiply 'a (multiply 'b (multiply 'c 'd)))
          second (multiply 'a (multiply (multiply 'b 'c) 'd))
          third (multiply 'a (multiply (multiply 'c 'b) 'd))
          fourth (multiply 'a (multiply 'c (multiply 'b 'd)))
          finish (multiply (multiply 'a 'c) (multiply 'b 'd))
          step-one
          (function/app (function/const* 'nnrat/multiply-associative [])
                        'a 'b (multiply 'c 'd))
          step-two
          (multiply-respects
           'a 'a (multiply 'b (multiply 'c 'd))
           (multiply (multiply 'b 'c) 'd)
           (equivalent-reflexive 'a)
           (equivalent-symmetric
            (multiply (multiply 'b 'c) 'd)
            (multiply 'b (multiply 'c 'd))
            (function/app (function/const* 'nnrat/multiply-associative [])
                          'b 'c 'd)))
          step-three
          (multiply-respects
           'a 'a (multiply (multiply 'b 'c) 'd)
           (multiply (multiply 'c 'b) 'd)
           (equivalent-reflexive 'a)
           (multiply-respects
            (multiply 'b 'c) (multiply 'c 'b) 'd 'd
            (function/app (function/const* 'nnrat/multiply-commutative [])
                          'b 'c)
            (equivalent-reflexive 'd)))
          step-four
          (multiply-respects
           'a 'a (multiply (multiply 'c 'b) 'd)
           (multiply 'c (multiply 'b 'd))
           (equivalent-reflexive 'a)
           (function/app (function/const* 'nnrat/multiply-associative [])
                         'c 'b 'd))
          step-five
          (equivalent-symmetric
           finish fourth
           (function/app (function/const* 'nnrat/multiply-associative [])
                         'a 'c (multiply 'b 'd)))
          through-two
          (equivalent-transitive start first second step-one step-two)
          through-three
          (equivalent-transitive start second third through-two step-three)
          through-four
          (equivalent-transitive start third fourth through-three step-four)]
      (equivalent-transitive start fourth finish through-four step-five)))})

(def theorem-specs
  [multiply-associative-spec multiply-swap-right-spec
   multiply-four-reorder-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nonnegative-rational reassociation failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :nnrat-product-reassociation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nonnegative-rational reassociation was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.product-reassociation))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
