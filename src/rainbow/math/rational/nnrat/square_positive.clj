(ns rainbow.math.rational.nnrat.square-positive
  "nnrat/square-positive : positive k -> positive (k*k). One step up the magnitude route to
  signed no-zero-divisors: nnrat/positive p reduces to strict-below 0 (numerator p), and
  numerator(k*k) is defeq numerator k * numerator k, so this is exactly nat/multiply-positive
  on the numerator."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.multiply-positive :as nat-mul-pos]
            [rainbow.math.rational.nnrat.positive-monotone :as nnrat-pos]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- app [f & a] (apply function/app f a))
(defn- positive [k] (app (function/const* 'nnrat/positive []) k))
(defn- numerator [k] (app (function/const* 'nnrat/numerator []) k))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- multiply [a b] (app (function/const* 'nnrat/multiply []) a b))
(defn- nat-multiply-positive [a b ha hb]
  (app (function/const* 'nat/multiply-positive []) a b ha hb))

(def square-positive-spec
  {:name 'nnrat/square-positive
   :universes []
   :type (function/forall [['k nnrat] ['hk (positive 'k)]] (positive (multiply 'k 'k)))
   :value (function/lam
           [['k nnrat] ['hk (positive 'k)]]
           ;; positive k :defeq strict-below 0 (num k); positive(k*k) :defeq strict-below 0
           ;; (num(k*k)) = strict-below 0 (num k * num k). So this is nat/multiply-positive.
           (nat-multiply-positive (numerator 'k) (numerator 'k) 'hk 'hk))})

(def theorem-specs [square-positive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      nat-mul-pos/extend-environment
      nnrat-pos/extend-environment
      (support/extend-with :nnrat-square-positive theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
