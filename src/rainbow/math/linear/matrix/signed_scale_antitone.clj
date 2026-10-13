(ns rainbow.math.linear.matrix.signed-scale-antitone
  "Nonpositive signed factors reverse scalar, vector, and matrix order.

  Negating a nonpositive factor makes it nonnegative.  Monotonicity for that
  factor, followed by order-reversing negation and the checked multiplication
  negation law, yields scalar multiplication antitonicity on both sides.  The
  scale-difference bridge and structural pointwise lifts extend the result to
  native vectors and matrices.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.pointwise-order-laws :as order-laws]
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
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
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
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(defn- negated-negative-product-equivalent [factor value]
  (let [negative-factor (signed-negate factor)
        negative-product (signed-multiply negative-factor value)
        product (signed-multiply factor value)
        negated-product (signed-negate negative-product)
        double-negated (signed-negate (signed-negate product))]
    (signed-transitive
     negated-product double-negated product
     (app (function/const* 'signed/negate-respects-equivalence [])
          negative-product (signed-negate product)
          (app (function/const* 'signed/multiply-negate-left [])
               factor value))
     (app (function/const* 'signed/negate-involutive []) product))))

(def multiply-left-antitone-spec
  {:name 'signed/multiply-left-antitone :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (signed-at-most
     (signed-multiply 'factor 'right)
     (signed-multiply 'factor 'left)))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (let [negative-factor (signed-negate 'factor)
          negated-zero (signed-negate signed-zero)
          negated-order
          (app (function/const* 'signed/negate-reverses-order [])
               'factor signed-zero 'factor-nonpositive)
          negative-factor-nonnegative
          (app (function/const* 'signed/at-most-respects-equivalence [])
               negated-zero signed-zero
               negative-factor negative-factor
               (function/const* 'signed/negate-zero [])
               (app (function/const* 'signed/equivalent-reflexive [])
                    negative-factor)
               negated-order)
          negative-left (signed-multiply negative-factor 'left)
          negative-right (signed-multiply negative-factor 'right)
          negative-products-ordered
          (app (function/const* 'signed/multiply-left-monotone [])
               negative-factor 'left 'right
               negative-factor-nonnegative 'ordered)
          reversed
          (app (function/const* 'signed/negate-reverses-order [])
               negative-left negative-right negative-products-ordered)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           (signed-negate negative-right)
           (signed-multiply 'factor 'right)
           (signed-negate negative-left)
           (signed-multiply 'factor 'left)
           (negated-negative-product-equivalent 'factor 'right)
           (negated-negative-product-equivalent 'factor 'left)
           reversed)))})

(def multiply-right-antitone-spec
  {:name 'signed/multiply-right-antitone :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (signed-at-most
     (signed-multiply 'right 'factor)
     (signed-multiply 'left 'factor)))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (let [source-left (signed-multiply 'factor 'right)
          source-right (signed-multiply 'factor 'left)
          target-left (signed-multiply 'right 'factor)
          target-right (signed-multiply 'left 'factor)
          source-order
          (app (function/const* 'signed/multiply-left-antitone [])
               'factor 'left 'right 'factor-nonpositive 'ordered)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           source-left target-left source-right target-right
           (app (function/const* 'signed/multiply-commutative [])
                'factor 'right)
           (app (function/const* 'signed/multiply-commutative [])
                'factor 'left)
           source-order)))})

(def scale-difference-antitone-spec
  {:name 'signed/scale-difference-antitone :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (signed-at-most
     (scale-difference 'factor 'right)
     (scale-difference 'factor 'left)))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (signed-at-most 'left 'right)]]
    (let [right-product (signed-multiply 'factor 'right)
          left-product (signed-multiply 'factor 'left)
          products-ordered
          (app (function/const* 'signed/multiply-left-antitone [])
               'factor 'left 'right 'factor-nonpositive 'ordered)]
      (app (function/const* 'signed/at-most-respects-equivalence [])
           right-product (scale-difference 'factor 'right)
           left-product (scale-difference 'factor 'left)
           (signed-symmetric
            (scale-difference 'factor 'right) right-product
            (app (function/const* 'signed/scale-difference-multiply [])
                 'factor 'right))
           (signed-symmetric
            (scale-difference 'factor 'left) left-product
            (app (function/const* 'signed/scale-difference-multiply [])
                 'factor 'left))
           products-ordered)))})

(def vector-signed-scale-antitone-spec
  {:name 'vector/signed-scale-antitone :universes []
   :type
   (function/forall
    [['factor signed] ['left vector-type] ['right vector-type]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-signed-scale 'factor 'right)
     (vector-signed-scale 'factor 'left)))
   :value
   (function/lam
    [['factor signed] ['left vector-type] ['right vector-type]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-signed-scale 'factor 'current-right)
             (vector-signed-scale 'factor 'current-left))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (vector-signed-scale 'factor 'current-right)
                   (vector-signed-scale 'factor empty))))]
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
            ['tail-antitone (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (vector-signed-scale 'factor 'current-right)
                    (vector-signed-scale 'factor current-left))))]
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
                     (scale-difference 'factor 'right-head)
                     (scale-difference 'factor 'left-head))
                    (vector-at-most
                     (vector-signed-scale 'factor 'right-tail)
                     (vector-signed-scale 'factor 'left-tail))
                    (app (function/const* 'signed/scale-difference-antitone [])
                         'factor 'left-head 'right-head
                         'factor-nonpositive
                         (proposition-left
                          head-order tail-order 'current-ordered))
                    (app 'tail-antitone 'right-tail
                         (proposition-right
                          head-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def matrix-signed-scale-antitone-spec
  {:name 'matrix/signed-scale-antitone :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most
     (matrix-signed-scale 'factor 'right)
     (matrix-signed-scale 'factor 'left)))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['factor-nonpositive (signed-at-most 'factor signed-zero)]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-ordered
              (matrix-at-most 'current-left 'current-right)]]
            (matrix-at-most
             (matrix-signed-scale 'factor 'current-right)
             (matrix-signed-scale 'factor 'current-left))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-ordered
                    (matrix-at-most empty 'current-right)]]
                  (matrix-at-most
                   (matrix-signed-scale 'factor 'current-right)
                   (matrix-signed-scale 'factor empty))))]
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
            ['tail-antitone (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-ordered
                     (matrix-at-most current-left 'current-right)]]
                   (matrix-at-most
                    (matrix-signed-scale 'factor 'current-right)
                    (matrix-signed-scale 'factor current-left))))]
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
                     (vector-signed-scale 'factor 'right-row)
                     (vector-signed-scale 'factor 'left-row))
                    (matrix-at-most
                     (matrix-signed-scale 'factor 'right-tail)
                     (matrix-signed-scale 'factor 'left-tail))
                    (app (function/const* 'vector/signed-scale-antitone [])
                         'factor 'left-row 'right-row
                         'factor-nonpositive
                         (proposition-left
                          row-order tail-order 'current-ordered))
                    (app 'tail-antitone 'right-tail
                         (proposition-right
                          row-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def definition-specs [])
(def theorem-specs
  [multiply-left-antitone-spec
   multiply-right-antitone-spec
   scale-difference-antitone-spec
   vector-signed-scale-antitone-spec
   matrix-signed-scale-antitone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      order-laws/extend-environment
      (support/extend-with :finite-matrix-signed-scale-antitone
                           theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
