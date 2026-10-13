(ns rainbow.math.rational.signed.decide-reflexive
  "Decision-level reflexivity for exact rational order.

  Order reflexivity alone does not determine which Boolean branch an executable
  selector takes on a tie. These theorems close that operational gap from the
  unary natural comparator through nnrat cross multiplication to signed cross
  sums: comparing a value with itself computes to true for every value, not
  merely for concrete numerals. Native and axiom-free on D63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- reflexive-bool [value]
  (app (function/const* 'equality/reflexive [type-level]) bool value))
(defn- decide-nat [left right]
  (app (function/const* 'nat/decide-at-most []) left right))
(defn- decide-nnrat [left right]
  (app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- decide-signed [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- numerator [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- multiply [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- add-nnrat [left right]
  (app (function/const* 'nnrat/add []) left right))

(def nat-decide-at-most-reflexive-true-spec
  {:name 'nat/decide-at-most-reflexive-true :universes []
   :type
   (function/forall
    [['value nat]]
    (eq-bool (decide-nat 'value 'value) true-value))
   :value
   (function/lam
    [['value nat]]
    (let [motive
          (function/lam
           [['candidate nat]]
           (eq-bool (decide-nat 'candidate 'candidate) true-value))]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (reflexive-bool true-value)
       (function/lam
        [['previous nat] ['induction-hypothesis (app motive 'previous)]]
        'induction-hypothesis)
       'value)))})

(def nnrat-decide-at-most-reflexive-true-spec
  {:name 'nnrat/decide-at-most-reflexive-true :universes []
   :type
   (function/forall
    [['value nnrat]]
    (eq-bool (decide-nnrat 'value 'value) true-value))
   :value
   (function/lam
    [['value nnrat]]
    (app
     (function/const* 'nat/decide-at-most-reflexive-true [])
     (multiply (numerator 'value) (denominator 'value))))})

(def signed-decide-at-most-reflexive-true-spec
  {:name 'signed/decide-at-most-reflexive-true :universes []
   :type
   (function/forall
    [['value signed]]
    (eq-bool (decide-signed 'value 'value) true-value))
   :value
   (function/lam
    [['value signed]]
    (app
     (function/const* 'nnrat/decide-at-most-reflexive-true [])
     (add-nnrat (positive 'value) (negative 'value))))})

(def definition-specs [])
(def theorem-specs
  [nat-decide-at-most-reflexive-true-spec
   nnrat-decide-at-most-reflexive-true-spec
   signed-decide-at-most-reflexive-true-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      decide/extend-environment
      (support/extend-with :signed-decide-reflexive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
