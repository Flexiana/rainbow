(ns rainbow.math.linear.matrix.signed-scale-order
  "Pointwise matrix order and monotonicity of signed module scaling.

  `matrix/at-most` is length-sensitive at both dimensions: corresponding rows
  must be pointwise ordered vectors and row counts must agree.  A nonnegative
  signed factor preserves scalar scale-difference order, and structural lifts
  preserve vector and matrix pointwise order.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-subtract :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.linear.vector.pointwise-order :as vector-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def truth (function/const* 'proposition/truth []))
(def falsity (function/const* 'proposition/falsity []))
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
(defn- matrix-prop [motive base step rows]
  (app (function/const* 'data/List.rec [type-level type-level])
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
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- matrix-at-most [left right]
  (app (function/const* 'matrix/at-most []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def matrix-at-most-spec
  {:name 'matrix/at-most :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type 'Prop)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      vector-type
      (function/lam
       [['ignored matrix-type]]
       (function/arrow matrix-type 'Prop))
      (function/lam
       [['current-right matrix-type]]
       (matrix-prop
        (function/lam [['ignored matrix-type]] 'Prop)
        truth
        (function/lam
         [['right-row vector-type] ['right-tail matrix-type]
          ['ignored 'Prop]]
         falsity)
        'current-right))
      (function/lam
       [['left-row vector-type] ['left-tail matrix-type]
        ['tail-relation (function/arrow matrix-type 'Prop)]]
       (function/lam
        [['current-right matrix-type]]
        (matrix-prop
         (function/lam [['ignored matrix-type]] 'Prop)
         falsity
         (function/lam
          [['right-row vector-type] ['right-tail matrix-type]
           ['ignored 'Prop]]
          (conjunction
           (vector-at-most 'left-row 'right-row)
           (app 'tail-relation 'right-tail)))
         'current-right)))
      'left)
     'right))})

(def scale-difference-monotone-spec
  {:name 'signed/scale-difference-monotone :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (signed-at-most 'left 'right)]]
    (signed-at-most
     (scale-difference 'factor 'left)
     (scale-difference 'factor 'right)))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (signed-at-most 'left 'right)]]
    (let [left-scale (scale-difference 'factor 'left)
          right-scale (scale-difference 'factor 'right)
          left-product (signed-multiply 'factor 'left)
          right-product (signed-multiply 'factor 'right)
          products-ordered
          (app (function/const* 'signed/multiply-left-monotone [])
               'factor 'left 'right 'factor-nonnegative 'ordered)
          left-product-scale
          (signed-symmetric
           left-scale left-product
           (app (function/const* 'signed/scale-difference-multiply [])
                'factor 'left))
          right-product-scale
          (signed-symmetric
           right-scale right-product
           (app (function/const* 'signed/scale-difference-multiply [])
                'factor 'right))]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           left-product left-scale right-product right-scale
           left-product-scale right-product-scale products-ordered)))})

(def vector-signed-scale-monotone-spec
  {:name 'vector/signed-scale-monotone :universes []
   :type
   (function/forall
    [['factor signed] ['left vector-type] ['right vector-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-signed-scale 'factor 'left)
     (vector-signed-scale 'factor 'right)))
   :value
   (function/lam
    [['factor signed] ['left vector-type] ['right vector-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-signed-scale 'factor 'current-left)
             (vector-signed-scale 'factor 'current-right))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (vector-signed-scale 'factor empty)
                   (vector-signed-scale 'factor 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              right-motive
              (function/lam
               [['current-ordered (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-ordered))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (vector-signed-scale 'factor current-left)
                    (vector-signed-scale 'factor 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               right-motive
               (function/lam
                [['current-ordered
                  (vector-at-most current-left (nil-vector))]]
                'current-ordered)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (vector-at-most
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-order
                       (signed-at-most 'left-head 'right-head)
                       tail-order
                       (vector-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (signed-at-most
                     (scale-difference 'factor 'left-head)
                     (scale-difference 'factor 'right-head))
                    (vector-at-most
                     (vector-signed-scale 'factor 'left-tail)
                     (vector-signed-scale 'factor 'right-tail))
                    (app
                     (function/const* 'signed/scale-difference-monotone [])
                     'factor 'left-head 'right-head 'factor-nonnegative
                     (proposition-left
                      head-order tail-order 'current-ordered))
                    (app 'tail-monotone 'right-tail
                         (proposition-right
                          head-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def matrix-at-most-empty-spec
  {:name 'matrix/at-most-empty :universes []
   :type (matrix-at-most (nil-matrix) (nil-matrix))
   :value trivial})

(def matrix-at-most-cons-spec
  {:name 'matrix/at-most-cons :universes []
   :type
   (function/forall
    [['left-row vector-type] ['right-row vector-type]
     ['left-tail matrix-type] ['right-tail matrix-type]
     ['row-ordered (vector-at-most 'left-row 'right-row)]
     ['tail-ordered (matrix-at-most 'left-tail 'right-tail)]]
    (matrix-at-most
     (cons-matrix 'left-row 'left-tail)
     (cons-matrix 'right-row 'right-tail)))
   :value
   (function/lam
    [['left-row vector-type] ['right-row vector-type]
     ['left-tail matrix-type] ['right-tail matrix-type]
     ['row-ordered (vector-at-most 'left-row 'right-row)]
     ['tail-ordered (matrix-at-most 'left-tail 'right-tail)]]
    (conjoin
     (vector-at-most 'left-row 'right-row)
     (matrix-at-most 'left-tail 'right-tail)
     'row-ordered 'tail-ordered))})

(def matrix-at-most-reflexive-spec
  {:name 'matrix/at-most-reflexive :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-at-most 'rows 'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-at-most 'current 'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-reflexive (matrix-at-most 'tail 'tail)]]
           (conjoin
            (vector-at-most 'row 'row)
            (matrix-at-most 'tail 'tail)
            (app (function/const* 'vector/at-most-reflexive []) 'row)
            'tail-reflexive))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-monotone-spec
  {:name 'matrix/signed-scale-monotone :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most
     (matrix-signed-scale 'factor 'left)
     (matrix-signed-scale 'factor 'right)))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['factor-nonnegative (signed-at-most signed-zero 'factor)]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-ordered
              (matrix-at-most 'current-left 'current-right)]]
            (matrix-at-most
             (matrix-signed-scale 'factor 'current-left)
             (matrix-signed-scale 'factor 'current-right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-ordered
                    (matrix-at-most empty 'current-right)]]
                  (matrix-at-most
                   (matrix-signed-scale 'factor empty)
                   (matrix-signed-scale 'factor 'current-right))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-ordered (matrix-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (matrix-at-most
                   empty (cons-matrix 'right-row 'right-tail))]]
                'current-ordered))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-ordered
                     (matrix-at-most current-left 'current-right)]]
                   (matrix-at-most
                    (matrix-signed-scale 'factor current-left)
                    (matrix-signed-scale 'factor 'current-right))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-ordered
                  (matrix-at-most current-left (nil-matrix))]]
                'current-ordered)
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (matrix-at-most
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [row-order
                       (vector-at-most 'left-row 'right-row)
                       tail-order
                       (matrix-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (vector-at-most
                     (vector-signed-scale 'factor 'left-row)
                     (vector-signed-scale 'factor 'right-row))
                    (matrix-at-most
                     (matrix-signed-scale 'factor 'left-tail)
                     (matrix-signed-scale 'factor 'right-tail))
                    (app
                     (function/const* 'vector/signed-scale-monotone [])
                     'factor 'left-row 'right-row 'factor-nonnegative
                     (proposition-left
                      row-order tail-order 'current-ordered))
                    (app 'tail-monotone 'right-tail
                         (proposition-right
                          row-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def definition-specs [matrix-at-most-spec])
(def theorem-specs
  [scale-difference-monotone-spec
   vector-signed-scale-monotone-spec
   matrix-at-most-empty-spec
   matrix-at-most-cons-spec
   matrix-at-most-reflexive-spec
   matrix-signed-scale-monotone-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      module/extend-environment
      (extend-spec-if-missing
       'vector/at-most :vector-pointwise-order
       vector-order/vector-at-most-spec)
      (extend-spec-if-missing
       'vector/at-most-reflexive :vector-pointwise-order
       vector-order/at-most-reflexive-spec)
      (extend-spec-if-missing
       'signed/multiply-left-monotone :signed-multiply-monotone
       multiply-monotone/multiply-left-monotone-spec)
      (extend-spec-if-missing
       'signed/at-most-respects-equivalence :signed-order-respects
       order-respects/at-most-respects-equivalence-spec)
      (support/extend-with :finite-matrix-signed-scale-order
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
