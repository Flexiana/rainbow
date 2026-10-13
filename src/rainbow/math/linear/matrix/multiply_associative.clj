(ns rainbow.math.linear.matrix.multiply-associative
  "Associativity of composable native finite matrix multiplication.

  For a nonempty middle matrix, composability of A*B and B*C entails

      (A*B)*C  ~  A*(B*C).

  The nonempty premise is exact for the row-list representation: an empty
  middle matrix can erase an output width that a later multiplication would
  otherwise recover.  The proof lifts transpose/action associativity across
  explicit columns, transports through the certified transpose/product bridge,
  and then maps the row theorem over A.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.transpose-multiply :as transpose-product]
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
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- composable [left right]
  (app (function/const* 'matrix/composable []) left right))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- column-action [rows columns]
  (app (function/const* 'matrix/column-action []) rows columns))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- vector-symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))

(def column-action-associative-spec
  {:name 'matrix/vector-multiply-column-action-associative :universes []
   :type
   (function/forall
    [['rows matrix-type] ['columns matrix-type]
     ['coefficients vector-type] ['reference vector-type]
     ['coefficient-shape
      (same-shape 'coefficients (column-shape 'rows))]
     ['rows-compatible (compatible 'rows 'reference)]
     ['columns-compatible (compatible 'columns 'reference)]]
    (vector-equivalent
     (vector-multiply
      'columns
      (vector-multiply (transpose 'rows) 'coefficients))
     (vector-multiply
      (column-action 'rows 'columns) 'coefficients)))
   :value
   (function/lam
    [['rows matrix-type] ['columns matrix-type]
     ['coefficients vector-type] ['reference vector-type]
     ['coefficient-shape
      (same-shape 'coefficients (column-shape 'rows))]
     ['rows-compatible (compatible 'rows 'reference)]
     ['columns-compatible (compatible 'columns 'reference)]]
    (let [transposed-action
          (vector-multiply (transpose 'rows) 'coefficients)
          motive
          (function/lam
           [['current-columns matrix-type]]
           (function/arrow
            (compatible 'current-columns 'reference)
            (vector-equivalent
             (vector-multiply 'current-columns transposed-action)
             (vector-multiply
              (column-action 'rows 'current-columns) 'coefficients))))
          step
          (function/lam
           [['column vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-compatible
              (compatible (cons-matrix 'column 'tail) 'reference)]]
            (let [column-reference-shape
                  (app (function/const* 'matrix/compatible-head-shape [])
                       'column 'tail 'reference 'current-compatible)
                  reference-column-shape
                  (same-shape-symmetric
                   'column 'reference column-reference-shape)
                  rows-column-compatible
                  (app (function/const* 'matrix/compatible-transport [])
                       'rows 'reference 'column
                       reference-column-shape 'rows-compatible)
                  tail-compatible
                  (app (function/const* 'matrix/compatible-tail [])
                       'column 'tail 'reference 'current-compatible)
                  start (dot 'column transposed-action)
                  commuted (dot transposed-action 'column)
                  associated
                  (dot
                   'coefficients (vector-multiply 'rows 'column))
                  finish
                  (dot
                   (vector-multiply 'rows 'column) 'coefficients)
                  head-same
                  (signed-transitive
                   start associated finish
                   (signed-transitive
                    start commuted associated
                    (app (function/const* 'vector/dot-commutative [])
                         'column transposed-action)
                    (app
                     (function/const*
                      'matrix/vector-action-associative [])
                     'rows 'coefficients 'column
                     'coefficient-shape rows-column-compatible))
                   (app (function/const* 'vector/dot-commutative [])
                        'coefficients
                        (vector-multiply 'rows 'column)))]
              (conjoin
               (signed-equivalent start finish)
               (vector-equivalent
                (vector-multiply 'tail transposed-action)
                (vector-multiply
                 (column-action 'rows 'tail) 'coefficients))
               head-same
               (app 'tail-law tail-compatible)))))]
      (app
       (matrix-rec
        motive
        (function/lam
         [['empty-compatible
           (compatible
            (app (function/const* 'data/nil [type-level]) vector-type)
            'reference)]]
         trivial)
        step 'columns)
       'columns-compatible)))})

(def multiply-row-associative-spec
  {:name 'matrix/multiply-row-associative :universes []
   :type
   (function/forall
    [['middle-head vector-type] ['middle-tail matrix-type]
     ['right matrix-type] ['coefficients vector-type]
     ['reference vector-type]
     ['coefficient-shape
      (same-shape
       'coefficients
       (column-shape (cons-matrix 'middle-head 'middle-tail)))]
     ['middle-compatible
      (compatible
       (cons-matrix 'middle-head 'middle-tail) 'reference)]
     ['columns-compatible
      (compatible (transpose 'right) 'reference)]]
    (vector-equivalent
     (vector-multiply
      (transpose 'right)
      (vector-multiply
       (transpose (cons-matrix 'middle-head 'middle-tail))
       'coefficients))
     (vector-multiply
      (transpose
       (multiply
        (cons-matrix 'middle-head 'middle-tail) 'right))
      'coefficients)))
   :value
   (function/lam
    [['middle-head vector-type] ['middle-tail matrix-type]
     ['right matrix-type] ['coefficients vector-type]
     ['reference vector-type]
     ['coefficient-shape
      (same-shape
       'coefficients
       (column-shape (cons-matrix 'middle-head 'middle-tail)))]
     ['middle-compatible
      (compatible
       (cons-matrix 'middle-head 'middle-tail) 'reference)]
     ['columns-compatible
      (compatible (transpose 'right) 'reference)]]
    (let [middle (cons-matrix 'middle-head 'middle-tail)
          columns (transpose 'right)
          column-images (column-action middle columns)
          product-columns (transpose (multiply middle 'right))
          start
          (vector-multiply
           columns
           (vector-multiply (transpose middle) 'coefficients))
          middle-output
          (vector-multiply column-images 'coefficients)
          finish (vector-multiply product-columns 'coefficients)
          column-associative
          (app
           (function/const*
            'matrix/vector-multiply-column-action-associative [])
           middle columns 'coefficients 'reference
           'coefficient-shape 'middle-compatible 'columns-compatible)
          transpose-product-same
          (app
           (function/const*
            'matrix/transpose-multiply-nonempty-left [])
           'middle-head 'middle-tail 'right)
          product-action-same
          (app
           (function/const*
            'matrix/vector-multiply-respects-matrix-equivalence [])
           product-columns column-images 'coefficients
           transpose-product-same)]
      (vector-transitive
       start middle-output finish
       column-associative
       (vector-symmetric
        finish middle-output product-action-same))))})

(def multiply-associative-spec
  {:name 'matrix/multiply-associative-nonempty-middle :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['left-middle-composable
      (composable
       'left (cons-matrix 'middle-head 'middle-tail))]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (matrix-equivalent
     (multiply
      (multiply
       'left (cons-matrix 'middle-head 'middle-tail))
      'right)
     (multiply
      'left
      (multiply
       (cons-matrix 'middle-head 'middle-tail) 'right))))
   :value
   (function/lam
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['left-middle-composable
      (composable
       'left (cons-matrix 'middle-head 'middle-tail))]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (let [middle (cons-matrix 'middle-head 'middle-tail)
          reference (column-shape 'right)
          left-middle-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               'left middle 'left-middle-composable)
          middle-reference-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               middle 'right 'middle-right-composable)
          right-rectangular
          (app (function/const* 'matrix/composable-right-rectangular [])
               middle 'right 'middle-right-composable)
          columns-compatible
          (app
           (function/const*
            'matrix/transpose-compatible-column-shape [])
           'right right-rectangular)
          motive
          (function/lam
           [['current-left matrix-type]]
           (function/arrow
            (compatible 'current-left (column-shape middle))
            (matrix-equivalent
             (multiply (multiply 'current-left middle) 'right)
             (multiply 'current-left (multiply middle 'right)))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-compatible
              (compatible
               (cons-matrix 'row 'tail) (column-shape middle))]]
            (let [row-shape
                  (app (function/const* 'matrix/compatible-head-shape [])
                       'row 'tail (column-shape middle)
                       'current-compatible)
                  tail-compatible
                  (app (function/const* 'matrix/compatible-tail [])
                       'row 'tail (column-shape middle)
                       'current-compatible)
                  row-same
                  (app (function/const* 'matrix/multiply-row-associative [])
                       'middle-head 'middle-tail 'right 'row reference
                       row-shape middle-reference-compatible
                       columns-compatible)]
              (conjoin
               (vector-equivalent
                (vector-multiply
                 (transpose 'right)
                 (vector-multiply (transpose middle) 'row))
                (vector-multiply
                 (transpose (multiply middle 'right)) 'row))
               (matrix-equivalent
                (multiply (multiply 'tail middle) 'right)
                (multiply 'tail (multiply middle 'right)))
               row-same
               (app 'tail-law tail-compatible)))))]
      (app
       (matrix-rec
        motive
        (function/lam
         [['empty-compatible
           (compatible
            (app (function/const* 'data/nil [type-level]) vector-type)
            (column-shape middle))]]
         trivial)
        step 'left)
       left-middle-compatible)))})

(def definition-specs [])
(def theorem-specs
  [column-action-associative-spec
   multiply-row-associative-spec
   multiply-associative-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      transpose-product/extend-environment
      (support/extend-with :finite-matrix-multiply-associative theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
