(ns rainbow.math.linear.vector.subtract-cancellation
  "Shape-safe cancellation through native vector subtraction.

  A common subtrahend cancels from equivalence and order.  A common minuend
  cancels from equivalence and reverses order, reflecting subtraction's
  antitone second argument.  The proofs reduce subtraction to addition plus
  negation and compose checked shape, addition-cancellation, and negation-
  reflection laws."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order :as signed-order]
            [rainbow.math.linear.vector.add-cancellation :as add-cancellation]
            [rainbow.math.linear.vector.equivalence-laws :as equivalence-laws]
            [rainbow.math.linear.vector.negate-reflection :as reflection]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))

(defn- shape-with-negated-offset [values offset values-shape]
  (let [negated (vector-negate offset)
        negated-offset
        (app (function/const* 'vector/negate-preserves-shape []) offset)
        offset-negated
        (app (function/const* 'vector/same-shape-symmetric [])
             negated offset negated-offset)]
    (app (function/const* 'vector/same-shape-transitive [])
         values offset negated values-shape offset-negated)))

(def equivalent-subtract-right-cancel-spec
  {:name 'vector/equivalent-subtract-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-subtract 'left 'offset)
       (vector-subtract 'right 'offset))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-subtract 'left 'offset)
       (vector-subtract 'right 'offset))]]
    (let [negated (vector-negate 'offset)]
      (app (function/const* 'vector/equivalent-add-right-cancel [])
           'left 'right negated
           (shape-with-negated-offset 'left 'offset 'left-shape)
           (shape-with-negated-offset 'right 'offset 'right-shape)
           'same)))})

(def at-most-subtract-right-cancel-spec
  {:name 'vector/at-most-subtract-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-subtract 'left 'offset)
       (vector-subtract 'right 'offset))]]
    (vector-at-most 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-subtract 'left 'offset)
       (vector-subtract 'right 'offset))]]
    (let [negated (vector-negate 'offset)]
      (app (function/const* 'vector/at-most-add-right-cancel [])
           'left 'right negated
           (shape-with-negated-offset 'left 'offset 'left-shape)
           (shape-with-negated-offset 'right 'offset 'right-shape)
           'ordered)))})

(defn- negated-shape-with-offset [values offset values-shape]
  (app (function/const* 'vector/same-shape-transitive [])
       (vector-negate values) values offset
       (app (function/const* 'vector/negate-preserves-shape []) values)
       values-shape))

(def equivalent-subtract-left-cancel-spec
  {:name 'vector/equivalent-subtract-left-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-subtract 'offset 'left)
       (vector-subtract 'offset 'right))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-subtract 'offset 'left)
       (vector-subtract 'offset 'right))]]
    (let [negated-left (vector-negate 'left)
          negated-right (vector-negate 'right)
          negated-same
          (app (function/const* 'vector/equivalent-add-left-cancel [])
               negated-left negated-right 'offset
               (negated-shape-with-offset 'left 'offset 'left-shape)
               (negated-shape-with-offset 'right 'offset 'right-shape)
               'same)]
      (app (function/const* 'vector/negate-reflects-equivalence [])
           'left 'right negated-same)))})

(def at-most-subtract-left-cancel-spec
  {:name 'vector/at-most-subtract-left-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-subtract 'offset 'left)
       (vector-subtract 'offset 'right))]]
    (vector-at-most 'right 'left))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-subtract 'offset 'left)
       (vector-subtract 'offset 'right))]]
    (let [negated-left (vector-negate 'left)
          negated-right (vector-negate 'right)
          negated-ordered
          (app (function/const* 'vector/at-most-add-left-cancel [])
               negated-left negated-right 'offset
               (negated-shape-with-offset 'left 'offset 'left-shape)
               (negated-shape-with-offset 'right 'offset 'right-shape)
               'ordered)]
      (app (function/const* 'vector/negate-reflects-order [])
           'left 'right negated-ordered)))})

(def definition-specs [])
(def theorem-specs
  [equivalent-subtract-right-cancel-spec
   at-most-subtract-right-cancel-spec
   equivalent-subtract-left-cancel-spec
   at-most-subtract-left-cancel-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-cancellation/extend-environment
      (extend-spec-if-missing
       'signed/negate-involutive :signed-order
       signed-order/negate-involutive-spec)
      (extend-spec-if-missing
       'vector/negate-involutive :vector-equivalence-laws
       equivalence-laws/negate-involutive-spec)
      (extend-spec-if-missing
       'vector/negate-reflects-order :vector-negate-reflection
       reflection/negate-reflects-order-spec)
      (extend-spec-if-missing
       'vector/negate-reflects-equivalence :vector-negate-reflection
       reflection/negate-reflects-equivalence-spec)
      (support/extend-with :vector-subtract-cancellation theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
