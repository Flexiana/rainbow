(ns rainbow.math.rational.signed.scale-order
  "Nonnegative-rational scaling preserves signed order.

    a <= b  ->  scale c a <= scale c b

  Signed order compares the two Grothendieck cross sums.  Scaling turns each
  into the corresponding cross sum multiplied by c; the verified nnrat ring
  normalizer supplies those distributive equivalences and native nnrat
  multiplication monotonicity supplies the central inequality."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.temporal-difference :as temporal-difference]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value] (app (function/const* 'signed/positive []) value))
(defn- negative [value] (app (function/const* 'signed/negative []) value))
(defn- scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- rat-at-most-respects [left left-prime right right-prime
                             left-same right-same ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))

(def scale-monotone-spec
  {:name 'signed/scale-monotone :universes []
   :type
   (function/forall
    [['rate nnrat] ['left signed] ['right signed]
     ['ordered (at-most 'left 'right)]]
    (at-most (scale 'rate 'left) (scale 'rate 'right)))
   :value
   (function/lam
    [['rate nnrat] ['left signed] ['right signed]
     ['ordered (at-most 'left 'right)]]
    (let [source-left (ring/radd (positive 'left) (negative 'right))
          source-right (ring/radd (positive 'right) (negative 'left))
          scaled-left (ring/rmul 'rate source-left)
          scaled-right (ring/rmul 'rate source-right)
          goal-left
          (ring/radd (ring/rmul 'rate (positive 'left))
                     (ring/rmul 'rate (negative 'right)))
          goal-right
          (ring/radd (ring/rmul 'rate (positive 'right))
                     (ring/rmul 'rate (negative 'left)))]
      (rat-at-most-respects
       goal-left scaled-left goal-right scaled-right
       (ring/equiv goal-left scaled-left)
       (ring/equiv goal-right scaled-right)
       (app (function/const* 'nnrat/multiply-monotone [])
            'rate source-left source-right 'ordered))))})

(def definition-specs [])
(def theorem-specs [scale-monotone-spec])

(defn- extend-scale-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment 'signed/scale)
    checked-environment
    (support/extend-with checked-environment :temporal-difference
                         [temporal-difference/scale-spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      extend-scale-if-missing
      ring/extend-environment
      multiply-monotone/extend-environment
      (support/extend-with :signed-scale-order theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
