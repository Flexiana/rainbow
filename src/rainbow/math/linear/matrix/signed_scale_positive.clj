(ns rainbow.math.linear.matrix.signed-scale-positive
  "Zero-value and nonnegativity laws for signed module scaling.

  Every signed factor sends scalar zero, vector zero-like, and matrix zero-like
  to zero up to the appropriate quotient equivalence.  Combined with
  nonnegative-factor monotonicity, this proves that signed scaling preserves
  scalar and entrywise vector/matrix zero lower bounds.  Native and axiom-free
  on D63."
  (:require [rainbow.math.linear.matrix.add-order :as order]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
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
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- matrix-zero-like [rows]
  (app (function/const* 'matrix/zero-like []) rows))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- matrix-at-most [left right]
  (app (function/const* 'matrix/at-most []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def scale-difference-zero-value-spec
  {:name 'signed/scale-difference-zero-value :universes []
   :type
   (function/forall
    [['factor signed]]
    (signed-equivalent
     (scale-difference 'factor signed-zero)
     signed-zero))
   :value
   (function/lam
    [['factor signed]]
    (let [start (scale-difference 'factor signed-zero)
          product (signed-multiply 'factor signed-zero)
          commuted (signed-multiply signed-zero 'factor)]
      (signed-transitive
       start commuted signed-zero
       (signed-transitive
        start product commuted
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor signed-zero)
        (app (function/const* 'signed/multiply-commutative [])
             'factor signed-zero))
       (app (function/const* 'signed/multiply-zero-left [])
            'factor))))})

(def vector-signed-scale-zero-like-spec
  {:name 'vector/signed-scale-zero-like :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale 'factor (vector-zero-like 'values))
     (vector-zero-like 'values)))
   :value
   (function/lam
    [['factor signed] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale 'factor (vector-zero-like 'current))
            (vector-zero-like 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-zero (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference 'factor signed-zero)
             signed-zero)
            (vector-equivalent
             (vector-signed-scale 'factor (vector-zero-like 'tail))
             (vector-zero-like 'tail))
            (app (function/const* 'signed/scale-difference-zero-value [])
                 'factor)
            'tail-zero))]
      (vector-rec motive trivial step 'values)))})

(def matrix-signed-scale-zero-like-spec
  {:name 'matrix/signed-scale-zero-like :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale 'factor (matrix-zero-like 'rows))
     (matrix-zero-like 'rows)))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale 'factor (matrix-zero-like 'current))
            (matrix-zero-like 'current)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-zero (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale 'factor (vector-zero-like 'row))
             (vector-zero-like 'row))
            (matrix-equivalent
             (matrix-signed-scale 'factor (matrix-zero-like 'tail))
             (matrix-zero-like 'tail))
            (app (function/const* 'vector/signed-scale-zero-like [])
                 'factor 'row)
            'tail-zero))]
      (matrix-rec motive trivial step 'rows)))})

(def scale-difference-nonnegative-spec
  {:name 'signed/scale-difference-nonnegative :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['value-nonnegative (signed-at-most signed-zero 'value)]]
    (signed-at-most
     signed-zero (scale-difference 'factor 'value)))
   :value
   (function/lam
    [['factor signed] ['value signed]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['value-nonnegative (signed-at-most signed-zero 'value)]]
    (let [scaled-zero (scale-difference 'factor signed-zero)
          scaled-value (scale-difference 'factor 'value)
          ordered
          (app (function/const* 'signed/scale-difference-monotone [])
               'factor signed-zero 'value
               'factor-nonnegative 'value-nonnegative)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           scaled-zero signed-zero scaled-value scaled-value
           (app (function/const* 'signed/scale-difference-zero-value [])
                'factor)
           (app (function/const* 'signed/equivalent-reflexive [])
                scaled-value)
           ordered)))})

(def vector-signed-scale-nonnegative-spec
  {:name 'vector/signed-scale-nonnegative :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['values-nonnegative
      (vector-at-most (vector-zero-like 'values) 'values)]]
    (vector-at-most
     (vector-zero-like 'values)
     (vector-signed-scale 'factor 'values)))
   :value
   (function/lam
    [['factor signed] ['values vector-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['values-nonnegative
      (vector-at-most (vector-zero-like 'values) 'values)]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (function/forall
            [['current-nonnegative
              (vector-at-most (vector-zero-like 'current) 'current)]]
            (vector-at-most
             (vector-zero-like 'current)
             (vector-signed-scale 'factor 'current))))
          base
          (function/lam
           [['current-nonnegative
             (vector-at-most
              (vector-zero-like
               (app (function/const* 'data/nil [type-level]) signed))
              (app (function/const* 'data/nil [type-level]) signed))]]
           trivial)
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-nonnegative (app motive 'tail)]]
           (function/lam
            [['current-nonnegative
              (vector-at-most
               (vector-zero-like
                (app (function/const* 'data/cons [type-level])
                     signed 'head 'tail))
               (app (function/const* 'data/cons [type-level])
                    signed 'head 'tail))]]
            (let [head-order (signed-at-most signed-zero 'head)
                  tail-order
                  (vector-at-most (vector-zero-like 'tail) 'tail)]
              (conjoin
               (signed-at-most
                signed-zero (scale-difference 'factor 'head))
               (vector-at-most
                (vector-zero-like 'tail)
                (vector-signed-scale 'factor 'tail))
               (app (function/const* 'signed/scale-difference-nonnegative [])
                    'factor 'head 'factor-nonnegative
                    (proposition-left
                     head-order tail-order 'current-nonnegative))
               (app 'tail-nonnegative
                    (proposition-right
                     head-order tail-order 'current-nonnegative))))))]
      (app (vector-rec motive base step 'values) 'values-nonnegative)))})

(def matrix-signed-scale-nonnegative-spec
  {:name 'matrix/signed-scale-nonnegative :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['rows-nonnegative
      (matrix-at-most (matrix-zero-like 'rows) 'rows)]]
    (matrix-at-most
     (matrix-zero-like 'rows)
     (matrix-signed-scale 'factor 'rows)))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['rows-nonnegative
      (matrix-at-most (matrix-zero-like 'rows) 'rows)]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (function/forall
            [['current-nonnegative
              (matrix-at-most (matrix-zero-like 'current) 'current)]]
            (matrix-at-most
             (matrix-zero-like 'current)
             (matrix-signed-scale 'factor 'current))))
          empty
          (app (function/const* 'data/nil [type-level]) vector-type)
          base
          (function/lam
           [['current-nonnegative
             (matrix-at-most (matrix-zero-like empty) empty)]]
           trivial)
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-nonnegative (app motive 'tail)]]
           (function/lam
            [['current-nonnegative
              (matrix-at-most
               (matrix-zero-like
                (app (function/const* 'data/cons [type-level])
                     vector-type 'row 'tail))
               (app (function/const* 'data/cons [type-level])
                    vector-type 'row 'tail))]]
            (let [row-order
                  (vector-at-most (vector-zero-like 'row) 'row)
                  tail-order
                  (matrix-at-most (matrix-zero-like 'tail) 'tail)]
              (conjoin
               (vector-at-most
                (vector-zero-like 'row)
                (vector-signed-scale 'factor 'row))
               (matrix-at-most
                (matrix-zero-like 'tail)
                (matrix-signed-scale 'factor 'tail))
               (app (function/const* 'vector/signed-scale-nonnegative [])
                    'factor 'row 'factor-nonnegative
                    (proposition-left
                     row-order tail-order 'current-nonnegative))
               (app 'tail-nonnegative
                    (proposition-right
                     row-order tail-order 'current-nonnegative))))))]
      (app (matrix-rec motive base step 'rows) 'rows-nonnegative)))})

(def definition-specs [])
(def theorem-specs
  [scale-difference-zero-value-spec
   vector-signed-scale-zero-like-spec
   matrix-signed-scale-zero-like-spec
   scale-difference-nonnegative-spec
   vector-signed-scale-nonnegative-spec
   matrix-signed-scale-nonnegative-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      order/extend-environment
      (support/extend-with :finite-matrix-signed-scale-positive
                           theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
