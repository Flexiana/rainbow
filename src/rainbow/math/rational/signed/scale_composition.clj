(ns rainbow.math.rational.signed.scale-composition
  "Composition of nonnegative scaling on signed rationals.

    scale outer (scale inner value)  ~  scale (outer * inner) value

  The two Grothendieck components differ only by nnrat multiplication
  association.  The verified nnrat ring normalizer emits the proof term."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.temporal-difference :as temporal-difference]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value] (app (function/const* 'signed/positive []) value))
(defn- negative [value] (app (function/const* 'signed/negative []) value))
(defn- scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))

(def scale-composition-spec
  {:name 'signed/scale-composition :universes []
   :type
   (function/forall
    [['outer nnrat] ['inner nnrat] ['value signed]]
    (equivalent
     (scale 'outer (scale 'inner 'value))
     (scale (ring/rmul 'outer 'inner) 'value)))
   :value
   (function/lam
    [['outer nnrat] ['inner nnrat] ['value signed]]
    (let [left-positive
          (ring/rmul 'outer (ring/rmul 'inner (positive 'value)))
          left-negative
          (ring/rmul 'outer (ring/rmul 'inner (negative 'value)))
          product (ring/rmul 'outer 'inner)
          right-positive (ring/rmul product (positive 'value))
          right-negative (ring/rmul product (negative 'value))]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def definition-specs [])
(def theorem-specs [scale-composition-spec])

(defn- extend-scale-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment 'signed/scale)
    checked-environment
    (support/extend-with checked-environment :temporal-difference
                         [temporal-difference/scale-spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      extend-scale-if-missing
      ring/extend-environment
      (support/extend-with :signed-scale-composition theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
