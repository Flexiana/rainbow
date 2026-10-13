(ns rainbow.math.linear.vector.norm-witness-laws
  "Transformation laws for exact native norm witnesses.

    signed/scale-square
    norm/is-norm-negate-vector
    norm/is-norm-scale

  Scaling a signed value by a nonnegative rate scales its square by rate^2.
  Consequently, exact perfect-square norm witnesses transport through vector
  scaling.  They also transport through vector negation because squared norm is
  invariant under componentwise negation."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.norm-laws :as laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nnrat-multiply [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- is-norm [values candidate]
  (app (function/const* 'norm/is-norm []) values candidate))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(def scale-square-spec
  {:name 'signed/scale-square :universes []
   :type
   (function/forall
    [['rate nnrat] ['value signed]]
    (signed-equivalent
     (signed-multiply
      (signed-scale 'rate 'value)
      (signed-scale 'rate 'value))
     (signed-scale
      (nnrat-multiply 'rate 'rate)
      (signed-multiply 'value 'value))))
   :value
   (function/lam
    [['rate nnrat] ['value signed]]
    (let [scaled (signed-scale 'rate 'value)
          square (signed-multiply 'value 'value)
          start (signed-multiply scaled scaled)
          first-scaled
          (signed-scale 'rate (signed-multiply 'value scaled))
          inner-start (signed-multiply 'value scaled)
          inner-commuted (signed-multiply scaled 'value)
          inner-finish (signed-scale 'rate square)
          twice-scaled (signed-scale 'rate inner-finish)
          finish
          (signed-scale (nnrat-multiply 'rate 'rate) square)
          inner-proof
          (transitive
           inner-start inner-commuted inner-finish
           (app (function/const* 'signed/multiply-commutative [])
                'value scaled)
           (app (function/const* 'signed/scale-multiply [])
                'rate 'value 'value))
          first-step
          (app (function/const* 'signed/scale-multiply [])
               'rate 'value scaled)
          second-step
          (app (function/const* 'signed/scale-respects-equivalence [])
               'rate inner-start inner-finish inner-proof)]
      (transitive
       start twice-scaled finish
       (transitive
        start first-scaled twice-scaled first-step second-step)
       (app (function/const* 'signed/scale-composition [])
            'rate 'rate square))))})

(def is-norm-negate-vector-spec
  {:name 'norm/is-norm-negate-vector :universes []
   :type
   (function/forall
    [['values vector-type] ['candidate signed]
     ['witness (is-norm 'values 'candidate)]]
    (is-norm (vector-negate 'values) 'candidate))
   :value
   (function/lam
    [['values vector-type] ['candidate signed]
     ['witness (is-norm 'values 'candidate)]]
    (let [candidate-square (signed-multiply 'candidate 'candidate)
          original-square (norm-squared 'values)
          negated-square (norm-squared (vector-negate 'values))]
      (transitive
       candidate-square original-square negated-square
       'witness
       (symmetric
        negated-square original-square
        (app (function/const* 'norm/norm-squared-negate [])
             'values)))))})

(def is-norm-scale-spec
  {:name 'norm/is-norm-scale :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type] ['candidate signed]
     ['witness (is-norm 'values 'candidate)]]
    (is-norm
     (vector-scale 'rate 'values)
     (signed-scale 'rate 'candidate)))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type] ['candidate signed]
     ['witness (is-norm 'values 'candidate)]]
    (let [factor (nnrat-multiply 'rate 'rate)
          candidate-square (signed-multiply 'candidate 'candidate)
          scaled-candidate (signed-scale 'rate 'candidate)
          start (signed-multiply scaled-candidate scaled-candidate)
          scaled-candidate-square (signed-scale factor candidate-square)
          scaled-vector-square
          (signed-scale factor (norm-squared 'values))
          finish (norm-squared (vector-scale 'rate 'values))
          transport-witness
          (app (function/const* 'signed/scale-respects-equivalence [])
               factor candidate-square (norm-squared 'values) 'witness)
          reverse-vector-scaling
          (symmetric
           finish scaled-vector-square
           (app (function/const* 'norm/norm-squared-scale [])
                'rate 'values))]
      (transitive
       start scaled-vector-square finish
       (transitive
        start scaled-candidate-square scaled-vector-square
        (app (function/const* 'signed/scale-square [])
             'rate 'candidate)
        transport-witness)
       reverse-vector-scaling)))})

(def definition-specs [])
(def theorem-specs
  [scale-square-spec
   is-norm-negate-vector-spec
   is-norm-scale-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      laws/extend-environment
      (support/extend-with :vector-norm-witness-laws theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
