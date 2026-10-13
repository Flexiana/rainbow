(ns rainbow.math.linear.vector.negate-reflection
  "Involutive vector negation reflects order and equivalence.

    -left <= -right  ->  right <= left
    -left ~  -right  ->  left ~ right

  Reverse the negated order once more, then transport through vector negation
  involutivity.  Equivalence reflection applies that result to both mutual
  bounds.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order :as signed-order]
            [rainbow.math.linear.vector.equivalence-laws :as equivalence-laws]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def negate-reflects-order-spec
  {:name 'vector/negate-reflects-order :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['ordered
      (vector-at-most
       (vector-negate 'left)
       (vector-negate 'right))]]
    (vector-at-most 'right 'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['ordered
      (vector-at-most
       (vector-negate 'left)
       (vector-negate 'right))]]
    (let [double-right (vector-negate (vector-negate 'right))
          double-left (vector-negate (vector-negate 'left))
          double-ordered
          (app (function/const* 'vector/negate-reverses-order [])
               (vector-negate 'left) (vector-negate 'right) 'ordered)
          right-involutive
          (app (function/const* 'vector/negate-involutive []) 'right)
          right-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               double-right 'right right-involutive)
          right-to-double
          (proposition-right
           (vector-at-most double-right 'right)
           (vector-at-most 'right double-right)
           right-bounds)
          left-involutive
          (app (function/const* 'vector/negate-involutive []) 'left)
          left-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               double-left 'left left-involutive)
          double-to-left
          (proposition-left
           (vector-at-most double-left 'left)
           (vector-at-most 'left double-left)
           left-bounds)]
      (app
       (function/const* 'vector/at-most-transitive [])
       'right double-left 'left
       (app (function/const* 'vector/at-most-transitive [])
            'right double-right double-left
            right-to-double double-ordered)
       double-to-left)))})

(def negate-reflects-equivalence-spec
  {:name 'vector/negate-reflects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same
      (vector-equivalent
       (vector-negate 'left)
       (vector-negate 'right))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same
      (vector-equivalent
       (vector-negate 'left)
       (vector-negate 'right))]]
    (let [bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               (vector-negate 'left) (vector-negate 'right) 'same)
          negated-forward
          (proposition-left
           (vector-at-most (vector-negate 'left) (vector-negate 'right))
           (vector-at-most (vector-negate 'right) (vector-negate 'left))
           bounds)
          negated-backward
          (proposition-right
           (vector-at-most (vector-negate 'left) (vector-negate 'right))
           (vector-at-most (vector-negate 'right) (vector-negate 'left))
           bounds)
          right-left
          (app (function/const* 'vector/negate-reflects-order [])
               'left 'right negated-forward)
          left-right
          (app (function/const* 'vector/negate-reflects-order [])
               'right 'left negated-backward)]
      (app (function/const* 'vector/at-most-antisymmetric [])
           'left 'right left-right right-left)))})

(def definition-specs [])
(def theorem-specs
  [negate-reflects-order-spec negate-reflects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      order-laws/extend-environment
      (extend-spec-if-missing
       'signed/negate-involutive :signed-order
       signed-order/negate-involutive-spec)
      (extend-spec-if-missing
       'vector/negate-involutive :vector-equivalence-laws
       equivalence-laws/negate-involutive-spec)
      (support/extend-with :vector-negate-reflection theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
