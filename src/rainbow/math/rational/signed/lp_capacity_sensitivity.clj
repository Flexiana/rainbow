(ns rainbow.math.rational.signed.lp-capacity-sensitivity
  "Capacity sensitivity for signed LP dual bounds.

  Moving capacities from b to b' changes the dual bound by at most the sum of
  exact distances between corresponding weighted capacity terms.  This form is
  valid for signed prices.  It is a checked output-bound theorem, not a claim
  about an LP executable or its numerical implementation."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.dot-commutative :as commutative]
            [rainbow.math.linear.vector.dot-distance-bound :as dot-distance]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [t]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- seqv [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- distance-sum [prices left right]
  (app (function/const* 'vector/dot-distance-sum [])
       prices left right))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- respects [left left* right right* left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left* right right* left-same right-same ordered))

(def capacity-bound-distance-spec
  (let [original-bound (dot 'capacities 'prices)
        changed-bound (dot 'changed-capacities 'prices)
        commuted-original (dot 'prices 'capacities)
        commuted-changed (dot 'prices 'changed-capacities)
        original-distance
        (scalar-distance original-bound changed-bound)
        commuted-distance
        (scalar-distance commuted-original commuted-changed)
        budget
        (distance-sum 'prices 'capacities 'changed-capacities)]
    {:name 'optimization/signed-lp-capacity-bound-distance
     :universes []
     :type
     (function/forall
      [['prices vector-type]
       ['capacities vector-type]
       ['changed-capacities vector-type]
       ['capacity-shape
        (same-shape 'capacities 'changed-capacities)]]
      (sle original-distance budget))
     :value
     (function/lam
      [['prices vector-type]
       ['capacities vector-type]
       ['changed-capacities vector-type]
       ['capacity-shape
        (same-shape 'capacities 'changed-capacities)]]
      (let [commuted-bound
            (app (function/const* 'vector/dot-distance-below-sum [])
                 'prices 'capacities 'changed-capacities
                 'capacity-shape)
            original-to-commuted
            (app
             (function/const* 'signed/distance-respects-equivalence [])
             original-bound commuted-original
             changed-bound commuted-changed
             (app (function/const* 'vector/dot-commutative [])
                  'capacities 'prices)
             (app (function/const* 'vector/dot-commutative [])
                  'changed-capacities 'prices))]
        (respects
         commuted-distance original-distance
         budget budget
         (symmetric original-distance commuted-distance
                    original-to-commuted)
         (reflexive budget)
         commuted-bound)))}))

(def capacity-bound-distance-bounded-spec
  (let [original-bound (dot 'capacities 'prices)
        changed-bound (dot 'changed-capacities 'prices)
        distance
        (scalar-distance original-bound changed-bound)
        budget
        (distance-sum 'prices 'capacities 'changed-capacities)]
    {:name 'optimization/signed-lp-capacity-bound-distance-bounded
     :universes []
     :type
     (function/forall
      [['prices vector-type]
       ['capacities vector-type]
       ['changed-capacities vector-type]
       ['upper signed]
       ['capacity-shape
        (same-shape 'capacities 'changed-capacities)]
       ['budget-bound (sle budget 'upper)]]
      (sle distance 'upper))
     :value
     (function/lam
      [['prices vector-type]
       ['capacities vector-type]
       ['changed-capacities vector-type]
       ['upper signed]
       ['capacity-shape
        (same-shape 'capacities 'changed-capacities)]
       ['budget-bound (sle budget 'upper)]]
      (transitive
       distance budget 'upper
       (app
        (function/const* 'optimization/signed-lp-capacity-bound-distance [])
        'prices 'capacities 'changed-capacities 'capacity-shape)
       'budget-bound))}))

(def theorem-specs
  [capacity-bound-distance-spec
   capacity-bound-distance-bounded-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      dot-distance/extend-environment
      commutative/extend-environment
      (support/extend-with :signed-lp-capacity-sensitivity theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
