(ns rainbow.math.linear.matrix.signed-scale-subtract
  "Negation and subtraction laws for signed multiplication and module scaling.

  Multiplication distributes over subtraction on either side.  Via the checked
  scale-difference/multiplication bridge, negating or subtracting either the
  factor or value commutes with signed scaling.  Structural vector and matrix
  lifts complete the same laws; value subtraction carries an exact-shape
  premise because native subtraction zips its two inputs.  Native and axiom-free
  on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-congruence :as congruence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.linear.vector.dot-subtract :as dot-subtract]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
(defn- matrix-subtract [left right]
  (app (function/const* 'matrix/subtract []) left right))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- vector-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))
(defn- matrix-shape-transitive [left middle right first second]
  (app (function/const* 'matrix/same-shape-transitive [])
       left middle right first second))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def multiply-subtract-left-spec
  {:name 'signed/multiply-subtract-left :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['factor signed]]
    (signed-equivalent
     (signed-multiply (signed-subtract 'left 'right) 'factor)
     (signed-subtract
      (signed-multiply 'left 'factor)
      (signed-multiply 'right 'factor))))
   :value
   (function/lam
    [['left signed] ['right signed] ['factor signed]]
    (let [negated-right (signed-negate 'right)
          left-product (signed-multiply 'left 'factor)
          negated-product
          (signed-multiply negated-right 'factor)
          right-product (signed-multiply 'right 'factor)
          start
          (signed-multiply (signed-subtract 'left 'right) 'factor)
          split (signed-add left-product negated-product)
          finish (signed-subtract left-product right-product)]
      (signed-transitive
       start split finish
       (app
        (function/const* 'signed/multiply-distributes-add-right [])
        'left negated-right 'factor)
       (app
        (function/const* 'signed/add-respects-equivalence [])
        left-product left-product
        negated-product (signed-negate right-product)
        (app (function/const* 'signed/equivalent-reflexive [])
             left-product)
        (app (function/const* 'signed/multiply-negate-left [])
             'right 'factor)))))})

(def multiply-subtract-right-spec
  {:name 'signed/multiply-subtract-right :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]]
    (signed-equivalent
     (signed-multiply 'factor (signed-subtract 'left 'right))
     (signed-subtract
      (signed-multiply 'factor 'left)
      (signed-multiply 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]]
    (let [difference (signed-subtract 'left 'right)
          start (signed-multiply 'factor difference)
          commuted (signed-multiply difference 'factor)
          split
          (signed-subtract
           (signed-multiply 'left 'factor)
           (signed-multiply 'right 'factor))
          finish
          (signed-subtract
           (signed-multiply 'factor 'left)
           (signed-multiply 'factor 'right))]
      (signed-transitive
       start split finish
       (signed-transitive
        start commuted split
        (app (function/const* 'signed/multiply-commutative [])
             'factor difference)
        (app (function/const* 'signed/multiply-subtract-left [])
             'left 'right 'factor))
       (app
        (function/const* 'signed/subtract-respects-equivalence [])
        (signed-multiply 'left 'factor)
        (signed-multiply 'factor 'left)
        (signed-multiply 'right 'factor)
        (signed-multiply 'factor 'right)
        (app (function/const* 'signed/multiply-commutative [])
             'left 'factor)
        (app (function/const* 'signed/multiply-commutative [])
             'right 'factor)))))})

(def scale-difference-negate-factor-spec
  {:name 'signed/scale-difference-negate-factor :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]]
    (signed-equivalent
     (scale-difference (signed-negate 'factor) 'value)
     (signed-negate (scale-difference 'factor 'value))))
   :value
   (function/lam
    [['factor signed] ['value signed]]
    (let [negated-factor (signed-negate 'factor)
          start (scale-difference negated-factor 'value)
          negated-product
          (signed-multiply negated-factor 'value)
          product (signed-multiply 'factor 'value)
          finish (signed-negate (scale-difference 'factor 'value))]
      (signed-transitive
       start (signed-negate product) finish
       (signed-transitive
        start negated-product (signed-negate product)
        (app (function/const* 'signed/scale-difference-multiply [])
             negated-factor 'value)
        (app (function/const* 'signed/multiply-negate-left [])
             'factor 'value))
       (app
        (function/const* 'signed/negate-respects-equivalence [])
        product (scale-difference 'factor 'value)
        (signed-symmetric
         (scale-difference 'factor 'value) product
         (app (function/const* 'signed/scale-difference-multiply [])
              'factor 'value))))))})

(def scale-difference-negate-value-spec
  {:name 'signed/scale-difference-negate-value :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]]
    (signed-equivalent
     (scale-difference 'factor (signed-negate 'value))
     (signed-negate (scale-difference 'factor 'value))))
   :value
   (function/lam
    [['factor signed] ['value signed]]
    (let [negated-value (signed-negate 'value)
          start (scale-difference 'factor negated-value)
          negated-product
          (signed-multiply 'factor negated-value)
          product (signed-multiply 'factor 'value)
          finish (signed-negate (scale-difference 'factor 'value))]
      (signed-transitive
       start (signed-negate product) finish
       (signed-transitive
        start negated-product (signed-negate product)
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor negated-value)
        (app (function/const* 'signed/multiply-negate-right [])
             'factor 'value))
       (app
        (function/const* 'signed/negate-respects-equivalence [])
        product (scale-difference 'factor 'value)
        (signed-symmetric
         (scale-difference 'factor 'value) product
         (app (function/const* 'signed/scale-difference-multiply [])
              'factor 'value))))))})

(def scale-difference-subtract-factor-spec
  {:name 'signed/scale-difference-subtract-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['value signed]]
    (signed-equivalent
     (scale-difference (signed-subtract 'left 'right) 'value)
     (signed-subtract
      (scale-difference 'left 'value)
      (scale-difference 'right 'value))))
   :value
   (function/lam
    [['left signed] ['right signed] ['value signed]]
    (let [difference (signed-subtract 'left 'right)
          start (scale-difference difference 'value)
          product (signed-multiply difference 'value)
          split
          (signed-subtract
           (signed-multiply 'left 'value)
           (signed-multiply 'right 'value))
          finish
          (signed-subtract
           (scale-difference 'left 'value)
           (scale-difference 'right 'value))]
      (signed-transitive
       start split finish
       (signed-transitive
        start product split
        (app (function/const* 'signed/scale-difference-multiply [])
             difference 'value)
        (app (function/const* 'signed/multiply-subtract-left [])
             'left 'right 'value))
       (app
        (function/const* 'signed/subtract-respects-equivalence [])
        (signed-multiply 'left 'value)
        (scale-difference 'left 'value)
        (signed-multiply 'right 'value)
        (scale-difference 'right 'value)
        (signed-symmetric
         (scale-difference 'left 'value)
         (signed-multiply 'left 'value)
         (app (function/const* 'signed/scale-difference-multiply [])
              'left 'value))
        (signed-symmetric
         (scale-difference 'right 'value)
         (signed-multiply 'right 'value)
         (app (function/const* 'signed/scale-difference-multiply [])
              'right 'value))))))})

(def scale-difference-subtract-value-spec
  {:name 'signed/scale-difference-subtract-value :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]]
    (signed-equivalent
     (scale-difference 'factor (signed-subtract 'left 'right))
     (signed-subtract
      (scale-difference 'factor 'left)
      (scale-difference 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]]
    (let [difference (signed-subtract 'left 'right)
          start (scale-difference 'factor difference)
          product (signed-multiply 'factor difference)
          split
          (signed-subtract
           (signed-multiply 'factor 'left)
           (signed-multiply 'factor 'right))
          finish
          (signed-subtract
           (scale-difference 'factor 'left)
           (scale-difference 'factor 'right))]
      (signed-transitive
       start split finish
       (signed-transitive
        start product split
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor difference)
        (app (function/const* 'signed/multiply-subtract-right [])
             'factor 'left 'right))
       (app
        (function/const* 'signed/subtract-respects-equivalence [])
        (signed-multiply 'factor 'left)
        (scale-difference 'factor 'left)
        (signed-multiply 'factor 'right)
        (scale-difference 'factor 'right)
        (signed-symmetric
         (scale-difference 'factor 'left)
         (signed-multiply 'factor 'left)
         (app (function/const* 'signed/scale-difference-multiply [])
              'factor 'left))
        (signed-symmetric
         (scale-difference 'factor 'right)
         (signed-multiply 'factor 'right)
         (app (function/const* 'signed/scale-difference-multiply [])
              'factor 'right))))))})

(def vector-signed-scale-negate-factor-spec
  {:name 'vector/signed-scale-negate-factor :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale (signed-negate 'factor) 'values)
     (vector-negate (vector-signed-scale 'factor 'values))))
   :value
   (function/lam
    [['factor signed] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale (signed-negate 'factor) 'current)
            (vector-negate (vector-signed-scale 'factor 'current))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference (signed-negate 'factor) 'head)
             (signed-negate (scale-difference 'factor 'head)))
            (vector-equivalent
             (vector-signed-scale (signed-negate 'factor) 'tail)
             (vector-negate (vector-signed-scale 'factor 'tail)))
            (app
             (function/const* 'signed/scale-difference-negate-factor [])
             'factor 'head)
            'tail-negates))]
      (vector-rec motive trivial step 'values)))})

(def vector-signed-scale-negate-value-spec
  {:name 'vector/signed-scale-negate-value :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale 'factor (vector-negate 'values))
     (vector-negate (vector-signed-scale 'factor 'values))))
   :value
   (function/lam
    [['factor signed] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale 'factor (vector-negate 'current))
            (vector-negate (vector-signed-scale 'factor 'current))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference 'factor (signed-negate 'head))
             (signed-negate (scale-difference 'factor 'head)))
            (vector-equivalent
             (vector-signed-scale 'factor (vector-negate 'tail))
             (vector-negate (vector-signed-scale 'factor 'tail)))
            (app
             (function/const* 'signed/scale-difference-negate-value [])
             'factor 'head)
            'tail-negates))]
      (vector-rec motive trivial step 'values)))})

(def vector-signed-scale-subtract-factor-spec
  {:name 'vector/signed-scale-subtract-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale (signed-subtract 'left 'right) 'values)
     (vector-subtract
      (vector-signed-scale 'left 'values)
      (vector-signed-scale 'right 'values))))
   :value
   (function/lam
    [['left signed] ['right signed] ['values vector-type]]
    (let [negated-right (signed-negate 'right)
          scaled-left (vector-signed-scale 'left 'values)
          scaled-negated
          (vector-signed-scale negated-right 'values)
          scaled-right (vector-signed-scale 'right 'values)
          start
          (vector-signed-scale (signed-subtract 'left 'right) 'values)
          split (vector-add scaled-left scaled-negated)
          finish (vector-subtract scaled-left scaled-right)]
      (vector-transitive
       start split finish
       (app
        (function/const* 'vector/signed-scale-additive-factor [])
        'left negated-right 'values)
       (app
        (function/const* 'vector/add-respects-equivalence [])
        scaled-left scaled-left
        scaled-negated (vector-negate scaled-right)
        (app (function/const* 'vector/equivalent-reflexive [])
             scaled-left)
        (app (function/const* 'vector/signed-scale-negate-factor [])
             'right 'values)))))})

(def vector-signed-scale-subtract-value-spec
  {:name 'vector/signed-scale-subtract-value :universes []
   :type
   (function/forall
    [['factor signed] ['left vector-type] ['right vector-type]
     ['same (vector-same-shape 'left 'right)]]
    (vector-equivalent
     (vector-signed-scale 'factor (vector-subtract 'left 'right))
     (vector-subtract
      (vector-signed-scale 'factor 'left)
      (vector-signed-scale 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left vector-type] ['right vector-type]
     ['same (vector-same-shape 'left 'right)]]
    (let [negated-right (vector-negate 'right)
          scaled-left (vector-signed-scale 'factor 'left)
          scaled-negated (vector-signed-scale 'factor negated-right)
          scaled-right (vector-signed-scale 'factor 'right)
          start
          (vector-signed-scale 'factor (vector-subtract 'left 'right))
          split (vector-add scaled-left scaled-negated)
          finish (vector-subtract scaled-left scaled-right)
          right-negated
          (app (function/const* 'vector/same-shape-symmetric [])
               negated-right 'right
               (app (function/const* 'vector/negate-preserves-shape [])
                    'right))
          left-negated
          (vector-shape-transitive
           'left 'right negated-right 'same right-negated)]
      (vector-transitive
       start split finish
       (app (function/const* 'vector/signed-scale-additive [])
            'factor 'left negated-right left-negated)
       (app
        (function/const* 'vector/add-respects-equivalence [])
        scaled-left scaled-left
        scaled-negated (vector-negate scaled-right)
        (app (function/const* 'vector/equivalent-reflexive [])
             scaled-left)
        (app (function/const* 'vector/signed-scale-negate-value [])
             'factor 'right)))))})

(def matrix-signed-scale-negate-factor-spec
  {:name 'matrix/signed-scale-negate-factor :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale (signed-negate 'factor) 'rows)
     (matrix-negate (matrix-signed-scale 'factor 'rows))))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale (signed-negate 'factor) 'current)
            (matrix-negate (matrix-signed-scale 'factor 'current))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale (signed-negate 'factor) 'row)
             (vector-negate (vector-signed-scale 'factor 'row)))
            (matrix-equivalent
             (matrix-signed-scale (signed-negate 'factor) 'tail)
             (matrix-negate (matrix-signed-scale 'factor 'tail)))
            (app (function/const* 'vector/signed-scale-negate-factor [])
                 'factor 'row)
            'tail-negates))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-negate-value-spec
  {:name 'matrix/signed-scale-negate-value :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale 'factor (matrix-negate 'rows))
     (matrix-negate (matrix-signed-scale 'factor 'rows))))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale 'factor (matrix-negate 'current))
            (matrix-negate (matrix-signed-scale 'factor 'current))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale 'factor (vector-negate 'row))
             (vector-negate (vector-signed-scale 'factor 'row)))
            (matrix-equivalent
             (matrix-signed-scale 'factor (matrix-negate 'tail))
             (matrix-negate (matrix-signed-scale 'factor 'tail)))
            (app (function/const* 'vector/signed-scale-negate-value [])
                 'factor 'row)
            'tail-negates))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-subtract-factor-spec
  {:name 'matrix/signed-scale-subtract-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale (signed-subtract 'left 'right) 'rows)
     (matrix-subtract
      (matrix-signed-scale 'left 'rows)
      (matrix-signed-scale 'right 'rows))))
   :value
   (function/lam
    [['left signed] ['right signed] ['rows matrix-type]]
    (let [negated-right (signed-negate 'right)
          scaled-left (matrix-signed-scale 'left 'rows)
          scaled-negated
          (matrix-signed-scale negated-right 'rows)
          scaled-right (matrix-signed-scale 'right 'rows)
          start
          (matrix-signed-scale (signed-subtract 'left 'right) 'rows)
          split (matrix-addition scaled-left scaled-negated)
          finish (matrix-subtract scaled-left scaled-right)]
      (matrix-transitive
       start split finish
       (app
        (function/const* 'matrix/signed-scale-additive-factor [])
        'left negated-right 'rows)
       (app
        (function/const* 'matrix/add-respects-equivalence [])
        scaled-left scaled-left
        scaled-negated (matrix-negate scaled-right)
        (app (function/const* 'matrix/equivalent-reflexive [])
             scaled-left)
        (app (function/const* 'matrix/signed-scale-negate-factor [])
             'right 'rows)))))})

(def matrix-signed-scale-subtract-value-spec
  {:name 'matrix/signed-scale-subtract-value :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (matrix-signed-scale 'factor (matrix-subtract 'left 'right))
     (matrix-subtract
      (matrix-signed-scale 'factor 'left)
      (matrix-signed-scale 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['same (matrix-same-shape 'left 'right)]]
    (let [negated-right (matrix-negate 'right)
          scaled-left (matrix-signed-scale 'factor 'left)
          scaled-negated (matrix-signed-scale 'factor negated-right)
          scaled-right (matrix-signed-scale 'factor 'right)
          start
          (matrix-signed-scale 'factor (matrix-subtract 'left 'right))
          split (matrix-addition scaled-left scaled-negated)
          finish (matrix-subtract scaled-left scaled-right)
          right-negated
          (app (function/const* 'matrix/same-shape-symmetric [])
               negated-right 'right
               (app
                (function/const* 'matrix/negate-preserves-same-shape [])
                'right))
          left-negated
          (matrix-shape-transitive
           'left 'right negated-right 'same right-negated)]
      (matrix-transitive
       start split finish
       (app (function/const* 'matrix/signed-scale-additive [])
            'factor 'left negated-right left-negated)
       (app
        (function/const* 'matrix/add-respects-equivalence [])
        scaled-left scaled-left
        scaled-negated (matrix-negate scaled-right)
        (app (function/const* 'matrix/equivalent-reflexive [])
             scaled-left)
        (app (function/const* 'matrix/signed-scale-negate-value [])
             'factor 'right)))))})

(def definition-specs [])
(def theorem-specs
  [multiply-subtract-left-spec
   multiply-subtract-right-spec
   scale-difference-negate-factor-spec
   scale-difference-negate-value-spec
   scale-difference-subtract-factor-spec
   scale-difference-subtract-value-spec
   vector-signed-scale-negate-factor-spec
   vector-signed-scale-negate-value-spec
   vector-signed-scale-subtract-factor-spec
   vector-signed-scale-subtract-value-spec
   matrix-signed-scale-negate-factor-spec
   matrix-signed-scale-negate-value-spec
   matrix-signed-scale-subtract-factor-spec
   matrix-signed-scale-subtract-value-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      congruence/extend-environment
      (extend-spec-if-missing
       'signed/multiply-distributes-add-right :signed-distributive
       distributive/multiply-distributes-add-right-spec)
      (extend-spec-if-missing
       'signed/multiply-negate-left :vector-dot-negate
       dot-negate/multiply-negate-left-spec)
      (extend-spec-if-missing
       'signed/multiply-negate-right :vector-dot-negate
       dot-negate/multiply-negate-right-spec)
      (extend-spec-if-missing
       'signed/subtract-respects-equivalence :vector-dot-subtract
       dot-subtract/subtract-respects-equivalence-spec)
      (support/extend-with :finite-matrix-signed-scale-subtract
                           theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
