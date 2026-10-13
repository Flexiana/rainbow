(ns rainbow.math.rational.signed.distance-multiply-nonnegative
  "Nonnegative signed multiplication bounds quotient-safe distance.

  Rather than requiring an absolute-value product theorem, the proof opens a
  distance bound into its two deviation rows.  Nonnegative multiplication
  preserves each row, distributivity identifies the scaled subtraction, and
  negation congruence identifies the reverse deviation.  Folding the rows back
  yields `d(w*x,w*y) <= w*d(x,y)` for `0 <= w`, exactly the component law needed
  by nonnegative matrix rows.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.signed-scale-subtract :as subtract]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance :as distance]
            [rainbow.math.rational.signed.multiply-monotone :as monotone]
            [rainbow.math.linear.vector.dot-negate :as negate]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- negate-value [value]
  (app (function/const* 'signed/negate []) value))
(defn- subtract-value [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- proposition-left [left right evidence]
  (app (function/const* 'proposition/left []) left right evidence))
(defn- proposition-right [left right evidence]
  (app (function/const* 'proposition/right []) left right evidence))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- equivalence-forward [left right iff evidence]
  (app (function/const* 'proposition/equivalence-forward [])
       left right iff evidence))
(defn- equivalence-backward [left right iff evidence]
  (app (function/const* 'proposition/equivalence-backward [])
       left right iff evidence))

(def distance-multiply-left-nonnegative-spec
  {:name 'signed/distance-multiply-left-nonnegative :universes []
   :type
   (function/forall
    [['weight signed] ['left signed] ['right signed]
     ['weight-nonnegative (sle signed-zero 'weight)]]
    (sle
     (scalar-distance (multiply 'weight 'left)
                      (multiply 'weight 'right))
     (multiply 'weight (scalar-distance 'left 'right))))
   :value
   (function/lam
    [['weight signed] ['left signed] ['right signed]
     ['weight-nonnegative (sle signed-zero 'weight)]]
    (let [delta (scalar-distance 'left 'right)
          difference (subtract-value 'left 'right)
          negated-difference (negate-value difference)
          scaled-delta (multiply 'weight delta)
          left-product (multiply 'weight 'left)
          right-product (multiply 'weight 'right)
          product-difference
          (subtract-value left-product right-product)
          negated-product-difference
          (negate-value product-difference)
          scaled-difference (multiply 'weight difference)
          scaled-negated-difference
          (multiply 'weight negated-difference)
          negated-scaled-difference
          (negate-value scaled-difference)
          source-bound (sle delta delta)
          source-forward-row (sle difference delta)
          source-reverse-row (sle negated-difference delta)
          source-rows
          (both source-forward-row source-reverse-row)
          source-iff
          (app
           (function/const*
            'signed/distance-bounded-iff-deviation-rows [])
           'left 'right delta)
          rows
          (equivalence-forward
           source-bound source-rows source-iff
           (order-reflexive delta))
          scaled-forward-bound
          (app (function/const* 'signed/multiply-left-monotone [])
               'weight difference delta
               'weight-nonnegative
               (proposition-left
                source-forward-row source-reverse-row rows))
          scaled-reverse-bound
          (app (function/const* 'signed/multiply-left-monotone [])
               'weight negated-difference delta
               'weight-nonnegative
               (proposition-right
                source-forward-row source-reverse-row rows))
          scaled-difference-same
          (app (function/const* 'signed/multiply-subtract-right [])
               'weight 'left 'right)
          scaled-negated-same
          (app (function/const* 'signed/multiply-negate-right [])
               'weight difference)
          negated-product-same
          (app
           (function/const* 'signed/negate-respects-equivalence [])
           scaled-difference product-difference
           scaled-difference-same)
          reverse-same
          (equivalent-transitive
           scaled-negated-difference negated-scaled-difference
           negated-product-difference
           scaled-negated-same negated-product-same)
          product-forward-bound
          (order-respects
           scaled-difference product-difference
           scaled-delta scaled-delta
           scaled-difference-same
           (equivalent-reflexive scaled-delta)
           scaled-forward-bound)
          product-reverse-bound
          (order-respects
           scaled-negated-difference negated-product-difference
           scaled-delta scaled-delta
           reverse-same
           (equivalent-reflexive scaled-delta)
           scaled-reverse-bound)
          product-bound
          (sle (scalar-distance left-product right-product)
               scaled-delta)
          product-rows
          (both (sle product-difference scaled-delta)
                (sle negated-product-difference scaled-delta))
          product-iff
          (app
           (function/const*
            'signed/distance-bounded-iff-deviation-rows [])
           left-product right-product scaled-delta)]
      (equivalence-backward
       product-bound product-rows product-iff
       (conjoin
        (sle product-difference scaled-delta)
        (sle negated-product-difference scaled-delta)
        product-forward-bound product-reverse-bound))))})

(def definition-specs [])
(def theorem-specs [distance-multiply-left-nonnegative-spec])

(defn extend-environment [env]
  (-> env
      distance/extend-environment
      monotone/extend-environment
      negate/extend-environment
      subtract/extend-environment
      (support/extend-with :signed-distance-multiply-nonnegative
                           theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
