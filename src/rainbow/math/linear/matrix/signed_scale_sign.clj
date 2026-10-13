(ns rainbow.math.linear.matrix.signed-scale-sign
  "The remaining sign combinations for signed scalar, vector, and matrix scaling.

  Nonnegative factor times nonpositive value and nonpositive factor times
  nonnegative value are nonpositive; nonpositive factor times nonpositive value
  is nonnegative.  Scalar proofs use monotonicity/antitonicity against zero and
  the arbitrary-factor zero law.  Two small proof-data generators lift each
  checked scalar rule structurally to vectors and matrices.  Native and
  axiom-free on D63."
  (:require [rainbow.math.linear.matrix.signed-scale-positive :as positive]
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
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- positive-part [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative-part [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- matrix-zero-like [rows]
  (app (function/const* 'matrix/zero-like []) rows))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- matrix-at-most [left right]
  (app (function/const* 'matrix/at-most []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive-part factor) value)
   (scalar-scale (negative-part factor) value)))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(defn- signed-sign [nonnegative? value]
  (if nonnegative?
    (signed-at-most signed-zero value)
    (signed-at-most value signed-zero)))
(defn- vector-sign [nonnegative? values]
  (if nonnegative?
    (vector-at-most (vector-zero-like values) values)
    (vector-at-most values (vector-zero-like values))))
(defn- matrix-sign [nonnegative? rows]
  (if nonnegative?
    (matrix-at-most (matrix-zero-like rows) rows)
    (matrix-at-most rows (matrix-zero-like rows))))

(def scale-difference-nonpositive-of-nonnegative-factor-spec
  {:name 'signed/scale-difference-nonpositive-of-nonnegative-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most signed-zero 'factor)]
     ['value-sign (signed-at-most 'value signed-zero)]]
    (signed-at-most (scale-difference 'factor 'value) signed-zero))
   :value
   (function/lam
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most signed-zero 'factor)]
     ['value-sign (signed-at-most 'value signed-zero)]]
    (let [scaled-value (scale-difference 'factor 'value)
          scaled-zero (scale-difference 'factor signed-zero)
          ordered
          (app (function/const* 'signed/scale-difference-monotone [])
               'factor 'value signed-zero 'factor-sign 'value-sign)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           scaled-value scaled-value scaled-zero signed-zero
           (app (function/const* 'signed/equivalent-reflexive [])
                scaled-value)
           (app (function/const* 'signed/scale-difference-zero-value [])
                'factor)
           ordered)))})

(def scale-difference-nonpositive-of-nonpositive-factor-spec
  {:name 'signed/scale-difference-nonpositive-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most 'factor signed-zero)]
     ['value-sign (signed-at-most signed-zero 'value)]]
    (signed-at-most (scale-difference 'factor 'value) signed-zero))
   :value
   (function/lam
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most 'factor signed-zero)]
     ['value-sign (signed-at-most signed-zero 'value)]]
    (let [scaled-value (scale-difference 'factor 'value)
          scaled-zero (scale-difference 'factor signed-zero)
          ordered
          (app (function/const* 'signed/scale-difference-antitone [])
               'factor signed-zero 'value 'factor-sign 'value-sign)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           scaled-value scaled-value scaled-zero signed-zero
           (app (function/const* 'signed/equivalent-reflexive [])
                scaled-value)
           (app (function/const* 'signed/scale-difference-zero-value [])
                'factor)
           ordered)))})

(def scale-difference-nonnegative-of-nonpositive-factor-spec
  {:name 'signed/scale-difference-nonnegative-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most 'factor signed-zero)]
     ['value-sign (signed-at-most 'value signed-zero)]]
    (signed-at-most signed-zero (scale-difference 'factor 'value)))
   :value
   (function/lam
    [['factor signed] ['value signed]
     ['factor-sign (signed-at-most 'factor signed-zero)]
     ['value-sign (signed-at-most 'value signed-zero)]]
    (let [scaled-zero (scale-difference 'factor signed-zero)
          scaled-value (scale-difference 'factor 'value)
          ordered
          (app (function/const* 'signed/scale-difference-antitone [])
               'factor 'value signed-zero 'factor-sign 'value-sign)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           scaled-zero signed-zero scaled-value scaled-value
           (app (function/const* 'signed/scale-difference-zero-value [])
                'factor)
           (app (function/const* 'signed/equivalent-reflexive [])
                scaled-value)
           ordered)))})

(defn- vector-sign-lift-value
  [scalar-theorem factor-nonnegative? values-nonnegative?
   result-nonnegative?]
  (function/lam
   [['factor signed] ['values vector-type]
    ['factor-sign (signed-sign factor-nonnegative? 'factor)]
    ['values-sign (vector-sign values-nonnegative? 'values)]]
   (let [motive
         (function/lam
          [['current vector-type]]
          (function/forall
           [['current-sign (vector-sign values-nonnegative? 'current)]]
           (vector-sign
            result-nonnegative?
            (vector-signed-scale 'factor 'current))))
         empty (nil-vector)
         base
         (function/lam
          [['current-sign (vector-sign values-nonnegative? empty)]]
          trivial)
         step
         (function/lam
          [['head signed] ['tail vector-type]
           ['tail-result (app motive 'tail)]]
          (function/lam
           [['current-sign
             (vector-sign
              values-nonnegative? (cons-vector 'head 'tail))]]
           (let [head-sign (signed-sign values-nonnegative? 'head)
                 tail-sign (vector-sign values-nonnegative? 'tail)
                 scaled-head (scale-difference 'factor 'head)
                 scaled-tail (vector-signed-scale 'factor 'tail)]
             (conjoin
              (signed-sign result-nonnegative? scaled-head)
              (vector-sign result-nonnegative? scaled-tail)
              (app (function/const* scalar-theorem [])
                   'factor 'head 'factor-sign
                   (proposition-left
                    head-sign tail-sign 'current-sign))
              (app 'tail-result
                   (proposition-right
                    head-sign tail-sign 'current-sign))))))]
     (app (vector-rec motive base step 'values) 'values-sign))))

(def vector-signed-scale-nonpositive-of-nonnegative-factor-spec
  {:name 'vector/signed-scale-nonpositive-of-nonnegative-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]
     ['factor-sign (signed-sign true 'factor)]
     ['values-sign (vector-sign false 'values)]]
    (vector-sign false (vector-signed-scale 'factor 'values)))
   :value
   (vector-sign-lift-value
    'signed/scale-difference-nonpositive-of-nonnegative-factor
    true false false)})

(def vector-signed-scale-nonpositive-of-nonpositive-factor-spec
  {:name 'vector/signed-scale-nonpositive-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]
     ['factor-sign (signed-sign false 'factor)]
     ['values-sign (vector-sign true 'values)]]
    (vector-sign false (vector-signed-scale 'factor 'values)))
   :value
   (vector-sign-lift-value
    'signed/scale-difference-nonpositive-of-nonpositive-factor
    false true false)})

(def vector-signed-scale-nonnegative-of-nonpositive-factor-spec
  {:name 'vector/signed-scale-nonnegative-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]
     ['factor-sign (signed-sign false 'factor)]
     ['values-sign (vector-sign false 'values)]]
    (vector-sign true (vector-signed-scale 'factor 'values)))
   :value
   (vector-sign-lift-value
    'signed/scale-difference-nonnegative-of-nonpositive-factor
    false false true)})

(defn- matrix-sign-lift-value
  [vector-theorem factor-nonnegative? rows-nonnegative?
   result-nonnegative?]
  (function/lam
   [['factor signed] ['rows matrix-type]
    ['factor-sign (signed-sign factor-nonnegative? 'factor)]
    ['rows-sign (matrix-sign rows-nonnegative? 'rows)]]
   (let [motive
         (function/lam
          [['current matrix-type]]
          (function/forall
           [['current-sign (matrix-sign rows-nonnegative? 'current)]]
           (matrix-sign
            result-nonnegative?
            (matrix-signed-scale 'factor 'current))))
         empty (nil-matrix)
         base
         (function/lam
          [['current-sign (matrix-sign rows-nonnegative? empty)]]
          trivial)
         step
         (function/lam
          [['row vector-type] ['tail matrix-type]
           ['tail-result (app motive 'tail)]]
          (function/lam
           [['current-sign
             (matrix-sign
              rows-nonnegative? (cons-matrix 'row 'tail))]]
           (let [row-sign (vector-sign rows-nonnegative? 'row)
                 tail-sign (matrix-sign rows-nonnegative? 'tail)
                 scaled-row (vector-signed-scale 'factor 'row)
                 scaled-tail (matrix-signed-scale 'factor 'tail)]
             (conjoin
              (vector-sign result-nonnegative? scaled-row)
              (matrix-sign result-nonnegative? scaled-tail)
              (app (function/const* vector-theorem [])
                   'factor 'row 'factor-sign
                   (proposition-left
                    row-sign tail-sign 'current-sign))
              (app 'tail-result
                   (proposition-right
                    row-sign tail-sign 'current-sign))))))]
     (app (matrix-rec motive base step 'rows) 'rows-sign))))

(def matrix-signed-scale-nonpositive-of-nonnegative-factor-spec
  {:name 'matrix/signed-scale-nonpositive-of-nonnegative-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]
     ['factor-sign (signed-sign true 'factor)]
     ['rows-sign (matrix-sign false 'rows)]]
    (matrix-sign false (matrix-signed-scale 'factor 'rows)))
   :value
   (matrix-sign-lift-value
    'vector/signed-scale-nonpositive-of-nonnegative-factor
    true false false)})

(def matrix-signed-scale-nonpositive-of-nonpositive-factor-spec
  {:name 'matrix/signed-scale-nonpositive-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]
     ['factor-sign (signed-sign false 'factor)]
     ['rows-sign (matrix-sign true 'rows)]]
    (matrix-sign false (matrix-signed-scale 'factor 'rows)))
   :value
   (matrix-sign-lift-value
    'vector/signed-scale-nonpositive-of-nonpositive-factor
    false true false)})

(def matrix-signed-scale-nonnegative-of-nonpositive-factor-spec
  {:name 'matrix/signed-scale-nonnegative-of-nonpositive-factor
   :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]
     ['factor-sign (signed-sign false 'factor)]
     ['rows-sign (matrix-sign false 'rows)]]
    (matrix-sign true (matrix-signed-scale 'factor 'rows)))
   :value
   (matrix-sign-lift-value
    'vector/signed-scale-nonnegative-of-nonpositive-factor
    false false true)})

(def definition-specs [])
(def theorem-specs
  [scale-difference-nonpositive-of-nonnegative-factor-spec
   scale-difference-nonpositive-of-nonpositive-factor-spec
   scale-difference-nonnegative-of-nonpositive-factor-spec
   vector-signed-scale-nonpositive-of-nonnegative-factor-spec
   vector-signed-scale-nonpositive-of-nonpositive-factor-spec
   vector-signed-scale-nonnegative-of-nonpositive-factor-spec
   matrix-signed-scale-nonpositive-of-nonnegative-factor-spec
   matrix-signed-scale-nonpositive-of-nonpositive-factor-spec
   matrix-signed-scale-nonnegative-of-nonpositive-factor-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      positive/extend-environment
      (support/extend-with :finite-matrix-signed-scale-sign theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
