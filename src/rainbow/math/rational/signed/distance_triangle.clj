(ns rainbow.math.rational.signed.distance-triangle
  "Triangle laws for quotient-safe signed absolute value and distance.

  The scalar proof is split into reusable algebra: subtraction through an
  intermediate point, subadditivity of absolute value, and then the distance
  triangle inequality.  Signed equivalence, rather than structural equality,
  is used throughout.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.distance :as distance]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- absolute [value]
  (app (function/const* 'signed/absolute []) value))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- add-monotone [left left-prime right right-prime
                     left-order right-order]
  (app (function/const* 'signed/add-monotone [])
       left left-prime right right-prime left-order right-order))

(def subtract-chain-spec
  {:name 'signed/subtract-chain :universes []
   :type
   (function/forall
    [['left signed] ['middle signed] ['right signed]]
    (veq (subtract 'left 'right)
         (add (subtract 'left 'middle)
              (subtract 'middle 'right))))
   :value
   (function/lam
    [['left signed] ['middle signed] ['right signed]]
    (let [pl (positive 'left) nl (negative 'left)
          pm (positive 'middle) nm (negative 'middle)
          pr (positive 'right) nr (negative 'right)
          direct-positive (ring/radd pl nr)
          direct-negative (ring/radd nl pr)
          via-positive
          (ring/radd (ring/radd pl nm) (ring/radd pm nr))
          via-negative
          (ring/radd (ring/radd nl pm) (ring/radd nm pr))]
      (ring/equiv
       (ring/radd direct-positive via-negative)
       (ring/radd via-positive direct-negative))))})

(def absolute-add-triangle-spec
  {:name 'signed/absolute-add-triangle :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (sle (absolute (add 'left 'right))
         (add (absolute 'left) (absolute 'right))))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [sum (add 'left 'right)
          threshold (add (absolute 'left) (absolute 'right))
          distributed (add (negate 'left) (negate 'right))
          sum-bound
          (add-monotone
           'left (absolute 'left) 'right (absolute 'right)
           (app (function/const* 'signed/at-most-absolute []) 'left)
           (app (function/const* 'signed/at-most-absolute []) 'right))
          distributed-bound
          (add-monotone
           (negate 'left) (absolute 'left)
           (negate 'right) (absolute 'right)
           (app (function/const* 'signed/negate-at-most-absolute []) 'left)
           (app (function/const* 'signed/negate-at-most-absolute []) 'right))
          negated-sum (negate sum)
          negated-sum-bound
          (order-respects
           distributed negated-sum threshold threshold
           (equivalent-symmetric
            negated-sum distributed
            (app (function/const* 'signed/negate-additive [])
                 'left 'right))
           (equivalent-reflexive threshold)
           distributed-bound)]
      (app (function/const* 'optimization/deviation-rows-sound [])
           sum threshold sum-bound negated-sum-bound)))})

(def distance-triangle-spec
  {:name 'signed/distance-triangle :universes []
   :type
   (function/forall
    [['left signed] ['middle signed] ['right signed]]
    (sle (scalar-distance 'left 'right)
         (add (scalar-distance 'left 'middle)
              (scalar-distance 'middle 'right))))
   :value
   (function/lam
    [['left signed] ['middle signed] ['right signed]]
    (let [direct (subtract 'left 'right)
          left-leg (subtract 'left 'middle)
          right-leg (subtract 'middle 'right)
          via (add left-leg right-leg)
          direct-magnitude (absolute direct)
          via-magnitude (absolute via)
          threshold (add (absolute left-leg) (absolute right-leg))
          direct-via
          (app (function/const* 'signed/subtract-chain [])
               'left 'middle 'right)
          magnitudes-same
          (app (function/const* 'signed/absolute-respects-equivalence [])
               direct via direct-via)
          via-bound
          (app (function/const* 'signed/absolute-add-triangle [])
               left-leg right-leg)]
      (order-respects
       via-magnitude direct-magnitude threshold threshold
       (equivalent-symmetric direct-magnitude via-magnitude magnitudes-same)
       (equivalent-reflexive threshold)
       via-bound)))})

(def definition-specs [])
(def theorem-specs
  [subtract-chain-spec absolute-add-triangle-spec distance-triangle-spec])

(defn extend-environment [env]
  (-> env
      ring/extend-environment
      distance/extend-environment
      monotone/extend-environment
      (support/extend-with :signed-distance-triangle theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
