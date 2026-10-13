(ns rainbow.math.linear.matrix.negate-linear
  "Negation commutes with native matrix action, transpose, and multiplication.

  Row-wise action negation follows from dot negation.  A structural column
  insertion law transports pointwise negation through total transpose.  These
  bridges prove that negating either factor negates the native matrix product,
  without rectangularity or compatibility premises.  Native and axiom-free on
  D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.additive-group :as group]
            [rainbow.math.linear.matrix.linear :as linear]
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
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
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
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))

(def vector-multiply-negate-rows-spec
  {:name 'matrix/vector-multiply-negate-rows :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply (matrix-negate 'rows) 'values)
     (vector-negate (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply (matrix-negate 'current-rows) 'values)
            (vector-negate
             (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (dot (vector-negate 'row) 'values)
             (signed-negate (dot 'row 'values)))
            (vector-equivalent
             (vector-multiply (matrix-negate 'tail) 'values)
             (vector-negate (vector-multiply 'tail 'values)))
            (app (function/const* 'vector/dot-negate-left [])
                 'row 'values)
            'tail-negates))]
      (matrix-rec motive trivial step 'rows)))})

(def prepend-column-negate-spec
  {:name 'matrix/prepend-column-negate :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]]
    (matrix-equivalent
     (prepend-column
      (vector-negate 'values) (matrix-negate 'columns))
     (matrix-negate (prepend-column 'values 'columns))))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]]
    (let [motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]]
            (matrix-equivalent
             (prepend-column
              (vector-negate 'current-values)
              (matrix-negate 'current-columns))
             (matrix-negate
              (prepend-column 'current-values 'current-columns)))))
          base
          (function/lam
           [['current-columns matrix-type]]
           trivial)
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-negates (app motive 'tail)]]
           (let [columns-motive
                 (function/lam
                  [['current-columns matrix-type]]
                  (matrix-equivalent
                   (prepend-column
                    (vector-negate
                     (app (function/const* 'data/cons [type-level])
                          signed 'head 'tail))
                    (matrix-negate 'current-columns))
                   (matrix-negate
                    (prepend-column
                     (app (function/const* 'data/cons [type-level])
                          signed 'head 'tail)
                     'current-columns))))]
             (function/lam
              [['current-columns matrix-type]]
              (matrix-rec
               columns-motive
               (conjoin
                (vector-equivalent
                 (app (function/const* 'data/cons [type-level])
                      signed (signed-negate 'head)
                      (app (function/const* 'data/nil [type-level]) signed))
                 (app (function/const* 'data/cons [type-level])
                      signed (signed-negate 'head)
                      (app (function/const* 'data/nil [type-level]) signed)))
                (matrix-equivalent
                 (prepend-column (vector-negate 'tail) (nil-matrix))
                 (matrix-negate (prepend-column 'tail (nil-matrix))))
                (app (function/const* 'vector/equivalent-reflexive [])
                     (app (function/const* 'data/cons [type-level])
                          signed (signed-negate 'head)
                          (app (function/const* 'data/nil [type-level])
                               signed)))
                (app 'tail-negates (nil-matrix)))
               (function/lam
                [['column vector-type] ['remaining-columns matrix-type]
                 ['ignored (app columns-motive 'remaining-columns)]]
                (conjoin
                 (vector-equivalent
                  (app (function/const* 'data/cons [type-level])
                       signed (signed-negate 'head)
                       (vector-negate 'column))
                  (app (function/const* 'data/cons [type-level])
                       signed (signed-negate 'head)
                       (vector-negate 'column)))
                 (matrix-equivalent
                  (prepend-column
                   (vector-negate 'tail)
                   (matrix-negate 'remaining-columns))
                  (matrix-negate
                   (prepend-column 'tail 'remaining-columns)))
                 (app (function/const* 'vector/equivalent-reflexive [])
                      (app (function/const* 'data/cons [type-level])
                           signed (signed-negate 'head)
                           (vector-negate 'column)))
                 (app 'tail-negates 'remaining-columns)))
               'current-columns))))]
      (app (vector-rec motive base step 'values) 'columns)))})

(def transpose-negate-spec
  {:name 'matrix/transpose-negate :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (transpose (matrix-negate 'rows))
     (matrix-negate (transpose 'rows))))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (matrix-equivalent
            (transpose (matrix-negate 'current-rows))
            (matrix-negate (transpose 'current-rows))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (let [negated-row (vector-negate 'row)
                 start
                 (prepend-column
                  negated-row (transpose (matrix-negate 'tail)))
                 middle
                 (prepend-column
                  negated-row (matrix-negate (transpose 'tail)))
                 finish
                 (matrix-negate
                  (prepend-column 'row (transpose 'tail)))]
             (matrix-transitive
              start middle finish
              (app
               (function/const*
                'matrix/prepend-column-respects-matrix-equivalence [])
               negated-row
               (transpose (matrix-negate 'tail))
               (matrix-negate (transpose 'tail))
               'tail-negates)
              (app (function/const* 'matrix/prepend-column-negate [])
                   'row (transpose 'tail)))))]
      (matrix-rec motive trivial step 'rows)))})

(def multiply-negate-left-spec
  {:name 'matrix/multiply-negate-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (multiply (matrix-negate 'left) 'right)
     (matrix-negate (multiply 'left 'right))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (let [columns (transpose 'right)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply (matrix-negate 'current-left) 'right)
            (matrix-negate (multiply 'current-left 'right))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-multiply columns (vector-negate 'row))
             (vector-negate (vector-multiply columns 'row)))
            (matrix-equivalent
             (multiply (matrix-negate 'tail) 'right)
             (matrix-negate (multiply 'tail 'right)))
            (app (function/const* 'matrix/vector-multiply-negate [])
                 columns 'row)
            'tail-negates))]
      (matrix-rec motive trivial step 'left)))})

(def multiply-negate-right-spec
  {:name 'matrix/multiply-negate-right :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (multiply 'left (matrix-negate 'right))
     (matrix-negate (multiply 'left 'right))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (let [negated-transpose (transpose (matrix-negate 'right))
          transpose-negated (matrix-negate (transpose 'right))
          transpose-same
          (app (function/const* 'matrix/transpose-negate []) 'right)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply 'current-left (matrix-negate 'right))
            (matrix-negate (multiply 'current-left 'right))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (let [start (vector-multiply negated-transpose 'row)
                 middle (vector-multiply transpose-negated 'row)
                 finish
                 (vector-negate
                  (vector-multiply (transpose 'right) 'row))]
             (conjoin
              (vector-equivalent start finish)
              (matrix-equivalent
               (multiply 'tail (matrix-negate 'right))
               (matrix-negate (multiply 'tail 'right)))
              (vector-transitive
               start middle finish
               (app
                (function/const*
                 'matrix/vector-multiply-respects-matrix-equivalence [])
                negated-transpose transpose-negated 'row transpose-same)
               (app
                (function/const* 'matrix/vector-multiply-negate-rows [])
                (transpose 'right) 'row))
              'tail-negates)))]
      (matrix-rec motive trivial step 'left)))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-negate-rows-spec
   prepend-column-negate-spec
   transpose-negate-spec
   multiply-negate-left-spec
   multiply-negate-right-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      group/extend-environment
      (extend-spec-if-missing
       'matrix/vector-multiply-negate :finite-matrix-linear
       linear/vector-multiply-negate-spec)
      (support/extend-with :finite-matrix-negate-linear theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
