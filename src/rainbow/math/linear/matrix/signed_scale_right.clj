(ns rainbow.math.linear.matrix.signed-scale-right
  "The complementary half of arbitrary signed matrix bilinearity.

  Scaling every row of a native matrix scales its action.  Pointwise signed
  scaling also commutes with the total prepend-column operation, hence with
  total transpose even for ragged and empty matrices.  Together these facts
  prove unrestricted homogeneity in the right factor of matrix multiplication.
  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.signed-scale :as signed-scale]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
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
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
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
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def vector-multiply-signed-scale-rows-spec
  {:name 'matrix/vector-multiply-signed-scale-rows :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply (matrix-signed-scale 'factor 'rows) 'values)
     (vector-signed-scale
      'factor (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type] ['values vector-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply
             (matrix-signed-scale 'factor 'current-rows) 'values)
            (vector-signed-scale
             'factor (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-homogeneous (app motive 'tail)]]
           (let [row-dot (dot 'row 'values)
                 product (signed-multiply 'factor row-dot)
                 difference (scale-difference 'factor row-dot)]
             (conjoin
              (signed-equivalent
               (dot (vector-signed-scale 'factor 'row) 'values)
               difference)
              (vector-equivalent
               (vector-multiply
                (matrix-signed-scale 'factor 'tail) 'values)
               (vector-signed-scale
                'factor (vector-multiply 'tail 'values)))
              (signed-transitive
               (dot (vector-signed-scale 'factor 'row) 'values)
               product difference
               (app (function/const* 'vector/dot-signed-scale-left [])
                    'factor 'row 'values)
               (signed-symmetric
                difference product
                (app
                 (function/const* 'signed/scale-difference-multiply [])
                 'factor row-dot)))
              'tail-homogeneous)))]
      (matrix-rec motive trivial step 'rows)))})

(def prepend-column-signed-scale-spec
  {:name 'matrix/prepend-column-signed-scale :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type] ['columns matrix-type]]
    (matrix-equivalent
     (prepend-column
      (vector-signed-scale 'factor 'values)
      (matrix-signed-scale 'factor 'columns))
     (matrix-signed-scale
      'factor (prepend-column 'values 'columns))))
   :value
   (function/lam
    [['factor signed] ['values vector-type] ['columns matrix-type]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]]
            (matrix-equivalent
             (prepend-column
              (vector-signed-scale 'factor 'current-values)
              (matrix-signed-scale 'factor 'current-columns))
             (matrix-signed-scale
              'factor
              (prepend-column 'current-values 'current-columns)))))
          values-base
          (function/lam
           [['current-columns matrix-type]]
           trivial)
          values-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-commutes (app values-motive 'tail)]]
           (let [scaled-head (scale-difference 'factor 'head)
                 scaled-singleton
                 (cons-vector scaled-head (nil-vector))
                 columns-motive
                 (function/lam
                  [['current-columns matrix-type]]
                  (matrix-equivalent
                   (prepend-column
                    (vector-signed-scale
                     'factor (cons-vector 'head 'tail))
                    (matrix-signed-scale 'factor 'current-columns))
                   (matrix-signed-scale
                    'factor
                    (prepend-column
                     (cons-vector 'head 'tail) 'current-columns))))
                 columns-base
                 (conjoin
                  (vector-equivalent scaled-singleton scaled-singleton)
                  (matrix-equivalent
                   (prepend-column
                    (vector-signed-scale 'factor 'tail)
                    (nil-matrix))
                   (matrix-signed-scale
                    'factor (prepend-column 'tail (nil-matrix))))
                  (app (function/const* 'vector/equivalent-reflexive [])
                       scaled-singleton)
                  (app 'tail-commutes (nil-matrix)))
                 columns-step
                 (function/lam
                  [['column vector-type] ['remaining-columns matrix-type]
                   ['ignored (app columns-motive 'remaining-columns)]]
                  (let [scaled-column
                        (cons-vector
                         scaled-head
                         (vector-signed-scale 'factor 'column))]
                    (conjoin
                     (vector-equivalent scaled-column scaled-column)
                     (matrix-equivalent
                      (prepend-column
                       (vector-signed-scale 'factor 'tail)
                       (matrix-signed-scale
                        'factor 'remaining-columns))
                      (matrix-signed-scale
                       'factor
                       (prepend-column 'tail 'remaining-columns)))
                     (app
                      (function/const* 'vector/equivalent-reflexive [])
                      scaled-column)
                     (app 'tail-commutes 'remaining-columns))))]
             (function/lam
              [['current-columns matrix-type]]
              (matrix-rec
               columns-motive columns-base columns-step 'current-columns))))]
      (app (vector-rec values-motive values-base values-step 'values)
           'columns)))})

(def transpose-signed-scale-spec
  {:name 'matrix/transpose-signed-scale :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type]]
    (matrix-equivalent
     (transpose (matrix-signed-scale 'factor 'rows))
     (matrix-signed-scale 'factor (transpose 'rows))))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (matrix-equivalent
            (transpose (matrix-signed-scale 'factor 'current-rows))
            (matrix-signed-scale
             'factor (transpose 'current-rows))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-commutes (app motive 'tail)]]
           (let [scaled-row (vector-signed-scale 'factor 'row)
                 start
                 (prepend-column
                  scaled-row
                  (transpose (matrix-signed-scale 'factor 'tail)))
                 middle
                 (prepend-column
                  scaled-row
                  (matrix-signed-scale 'factor (transpose 'tail)))
                 finish
                 (matrix-signed-scale
                  'factor (prepend-column 'row (transpose 'tail)))]
             (matrix-transitive
              start middle finish
              (app
               (function/const*
                'matrix/prepend-column-respects-matrix-equivalence [])
               scaled-row
               (transpose (matrix-signed-scale 'factor 'tail))
               (matrix-signed-scale 'factor (transpose 'tail))
               'tail-commutes)
              (app (function/const* 'matrix/prepend-column-signed-scale [])
                   'factor 'row (transpose 'tail)))))]
      (matrix-rec motive trivial step 'rows)))})

(def multiply-signed-scale-right-spec
  {:name 'matrix/multiply-signed-scale-right :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (multiply 'left (matrix-signed-scale 'factor 'right))
     (matrix-signed-scale 'factor (multiply 'left 'right))))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]]
    (let [scaled-right-transpose
          (transpose (matrix-signed-scale 'factor 'right))
          scaled-transpose
          (matrix-signed-scale 'factor (transpose 'right))
          transpose-commutes
          (app (function/const* 'matrix/transpose-signed-scale [])
               'factor 'right)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply
             'current-left (matrix-signed-scale 'factor 'right))
            (matrix-signed-scale
             'factor (multiply 'current-left 'right))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-homogeneous (app motive 'tail)]]
           (let [start (vector-multiply scaled-right-transpose 'row)
                 middle (vector-multiply scaled-transpose 'row)
                 finish
                 (vector-signed-scale
                  'factor (vector-multiply (transpose 'right) 'row))]
             (conjoin
              (vector-equivalent start finish)
              (matrix-equivalent
               (multiply
                'tail (matrix-signed-scale 'factor 'right))
               (matrix-signed-scale
                'factor (multiply 'tail 'right)))
              (vector-transitive
               start middle finish
               (app
                (function/const*
                 'matrix/vector-multiply-respects-matrix-equivalence [])
                scaled-right-transpose scaled-transpose 'row
                transpose-commutes)
               (app
                (function/const*
                 'matrix/vector-multiply-signed-scale-rows [])
                'factor (transpose 'right) 'row))
              'tail-homogeneous)))]
      (matrix-rec motive trivial step 'left)))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-signed-scale-rows-spec
   prepend-column-signed-scale-spec
   transpose-signed-scale-spec
   multiply-signed-scale-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      signed-scale/extend-environment
      (support/extend-with :finite-matrix-signed-scale-right theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
