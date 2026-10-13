(ns rainbow.math.linear.matrix.transpose-multiply
  "Transpose/product structure for nonempty native finite matrices.

  matrix/column-action maps a matrix action over an explicit list of columns.
  For a nonempty left operand, transposing a native product is equivalent to
  applying the left matrix to every transposed right column.  Nonemptiness is
  exact: transposing a zero-row matrix loses the number of zero-width rows.
  A companion theorem certifies that every column of a rectangular matrix has
  its row-count shape.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.action-associative :as action]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
            [rainbow.math.linear.matrix.transpose-shape :as transpose-shape]
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
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- list-map [mapping values]
  (app (function/const* 'list/map [type-level type-level])
       vector-type vector-type mapping values))
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
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- column-action [rows columns]
  (app (function/const* 'matrix/column-action []) rows columns))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- same-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(def column-action-spec
  {:name 'matrix/column-action :kind :definition :universes []
   :type (function/arrow matrix-type matrix-type matrix-type)
   :value
   (function/lam
    [['rows matrix-type] ['columns matrix-type]]
    (list-map
     (function/lam
      [['column vector-type]]
      (vector-multiply 'rows 'column))
     'columns))})

(def transpose-compatible-column-shape-spec
  {:name 'matrix/transpose-compatible-column-shape :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['rows-rectangular (rectangular 'rows)]]
    (compatible (transpose 'rows) (column-shape 'rows)))
   :value
   (function/lam
    [['rows matrix-type]
     ['rows-rectangular (rectangular 'rows)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/arrow
            (rectangular 'current-rows)
            (compatible
             (transpose 'current-rows)
             (column-shape 'current-rows))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-compatible-law (app motive 'tail)]]
           (let [tail-motive
                 (function/lam
                  [['current-tail matrix-type]]
                  (function/forall
                   [['current-tail-law
                     (function/arrow
                      (rectangular 'current-tail)
                      (compatible
                       (transpose 'current-tail)
                       (column-shape 'current-tail)))]
                    ['current-rectangular
                     (rectangular
                      (cons-matrix 'row 'current-tail))]]
                   (compatible
                    (transpose (cons-matrix 'row 'current-tail))
                    (column-shape
                     (cons-matrix 'row 'current-tail)))))
                 tail-base
                 (function/lam
                  [['current-tail-law
                    (function/arrow
                     (rectangular (nil-matrix))
                     (compatible
                      (transpose (nil-matrix))
                      (column-shape (nil-matrix))))]
                   ['current-rectangular
                    (rectangular
                     (cons-matrix 'row (nil-matrix)))]]
                  (app
                   (function/const*
                    'matrix/prepend-column-empty-compatible-singleton [])
                   'row signed-zero))
                 tail-step
                 (function/lam
                  [['second vector-type] ['rest matrix-type]
                   ['ignored (app tail-motive 'rest)]]
                  (function/lam
                   [['current-tail-law
                     (function/arrow
                      (rectangular (cons-matrix 'second 'rest))
                      (compatible
                       (transpose (cons-matrix 'second 'rest))
                       (column-shape (cons-matrix 'second 'rest))))]
                    ['current-rectangular
                     (rectangular
                      (cons-matrix
                       'row (cons-matrix 'second 'rest)))]]
                   (let [tail (cons-matrix 'second 'rest)
                         tail-rectangular
                         (app (function/const* 'matrix/rectangular-tail [])
                              'row tail 'current-rectangular)
                         tail-compatible
                         (app 'current-tail-law tail-rectangular)
                         second-row-shape
                         (app
                          (function/const*
                           'matrix/compatible-head-shape [])
                          'second 'rest 'row 'current-rectangular)
                         row-second-shape
                         (same-shape-symmetric
                          'second 'row second-row-shape)
                         transpose-output-shape
                         (app
                          (function/const*
                           'matrix/prepend-column-output-shape [])
                          'second (transpose 'rest))
                         second-transpose-shape
                         (same-shape-symmetric
                          (column-shape (transpose tail)) 'second
                          transpose-output-shape)
                         width
                         (same-shape-transitive
                          'row 'second
                          (column-shape (transpose tail))
                          row-second-shape second-transpose-shape)]
                     (app
                      (function/const*
                       'matrix/prepend-column-preserves-compatibility [])
                      'row (transpose tail)
                      signed-zero (column-shape tail)
                      width tail-compatible))))]
             (function/lam
              [['current-rectangular
                (rectangular (cons-matrix 'row 'tail))]]
              (app
               (matrix-rec tail-motive tail-base tail-step 'tail)
               'tail-compatible-law 'current-rectangular))))]
      (app
       (matrix-rec
        motive
        (function/lam
         [['empty-rectangular (rectangular (nil-matrix))]]
         trivial)
        step 'rows)
       'rows-rectangular)))})

(def prepend-column-action-empty-spec
  {:name 'matrix/prepend-column-action-empty :universes []
   :type
   (function/forall
    [['row vector-type] ['columns matrix-type]]
    (matrix-equivalent
     (prepend-column
      (vector-multiply 'columns 'row) (nil-matrix))
     (column-action
      (cons-matrix 'row (nil-matrix)) 'columns)))
   :value
   (function/lam
    [['row vector-type] ['columns matrix-type]]
    (let [motive
          (function/lam
           [['current-columns matrix-type]]
           (matrix-equivalent
            (prepend-column
             (vector-multiply 'current-columns 'row) (nil-matrix))
            (column-action
             (cons-matrix 'row (nil-matrix)) 'current-columns)))
          step
          (function/lam
           [['column vector-type] ['remaining-columns matrix-type]
            ['tail-same (app motive 'remaining-columns)]]
           (let [left-row
                 (cons-vector (dot 'column 'row) (nil-vector))
                 right-row
                 (cons-vector (dot 'row 'column) (nil-vector))]
             (conjoin
              (vector-equivalent left-row right-row)
              (matrix-equivalent
               (prepend-column
                (vector-multiply 'remaining-columns 'row) (nil-matrix))
               (column-action
                (cons-matrix 'row (nil-matrix)) 'remaining-columns))
              (conjoin
               (signed-equivalent
                (dot 'column 'row) (dot 'row 'column))
               (vector-equivalent (nil-vector) (nil-vector))
               (app (function/const* 'vector/dot-commutative [])
                    'column 'row)
               trivial)
              'tail-same)))]
      (matrix-rec motive trivial step 'columns)))})

(def prepend-column-column-action-spec
  {:name 'matrix/prepend-column-column-action :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['columns matrix-type]]
    (matrix-equivalent
     (prepend-column
      (vector-multiply 'columns 'row)
      (column-action 'tail 'columns))
     (column-action (cons-matrix 'row 'tail) 'columns)))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['columns matrix-type]]
    (let [motive
          (function/lam
           [['current-columns matrix-type]]
           (matrix-equivalent
            (prepend-column
             (vector-multiply 'current-columns 'row)
             (column-action 'tail 'current-columns))
            (column-action
             (cons-matrix 'row 'tail) 'current-columns)))
          step
          (function/lam
           [['column vector-type] ['remaining-columns matrix-type]
            ['tail-same (app motive 'remaining-columns)]]
           (let [tail-action (vector-multiply 'tail 'column)
                 left-row
                 (cons-vector (dot 'column 'row) tail-action)
                 right-row
                 (cons-vector (dot 'row 'column) tail-action)]
             (conjoin
              (vector-equivalent left-row right-row)
              (matrix-equivalent
               (prepend-column
                (vector-multiply 'remaining-columns 'row)
                (column-action 'tail 'remaining-columns))
               (column-action
                (cons-matrix 'row 'tail) 'remaining-columns))
              (conjoin
               (signed-equivalent
                (dot 'column 'row) (dot 'row 'column))
               (vector-equivalent tail-action tail-action)
               (app (function/const* 'vector/dot-commutative [])
                    'column 'row)
               (app (function/const* 'vector/equivalent-reflexive [])
                    tail-action))
              'tail-same)))]
      (matrix-rec motive trivial step 'columns)))})

(def transpose-multiply-nonempty-left-spec
  {:name 'matrix/transpose-multiply-nonempty-left :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (transpose (multiply (cons-matrix 'row 'tail) 'right))
     (column-action
      (cons-matrix 'row 'tail) (transpose 'right))))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['right matrix-type]]
    (let [columns (transpose 'right)
          motive
          (function/lam
           [['current-tail matrix-type]]
           (function/forall
            [['current-row vector-type]]
            (matrix-equivalent
             (transpose
              (multiply
               (cons-matrix 'current-row 'current-tail) 'right))
             (column-action
              (cons-matrix 'current-row 'current-tail) columns))))
          base
          (function/lam
           [['current-row vector-type]]
           (app (function/const* 'matrix/prepend-column-action-empty [])
                'current-row columns))
          step
          (function/lam
           [['second vector-type] ['rest matrix-type]
            ['rest-law (app motive 'rest)]]
           (function/lam
            [['current-row vector-type]]
            (let [current-tail (cons-matrix 'second 'rest)
                  row-action (vector-multiply columns 'current-row)
                  tail-transposes (app 'rest-law 'second)
                  start
                  (prepend-column
                   row-action (transpose (multiply current-tail 'right)))
                  middle
                  (prepend-column
                   row-action (column-action current-tail columns))
                  finish
                  (column-action
                   (cons-matrix 'current-row current-tail) columns)]
              (matrix-transitive
               start middle finish
               (app
                (function/const*
                 'matrix/prepend-column-respects-matrix-equivalence [])
                row-action
                (transpose (multiply current-tail 'right))
                (column-action current-tail columns)
                tail-transposes)
               (app
                (function/const*
                 'matrix/prepend-column-column-action [])
                'current-row current-tail columns)))))]
      (app (matrix-rec motive base step 'tail) 'row)))})

(def definition-specs [column-action-spec])
(def theorem-specs
  [transpose-compatible-column-shape-spec
   prepend-column-action-empty-spec
   prepend-column-column-action-spec
   transpose-multiply-nonempty-left-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.action-associative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'matrix/rectangular-tail :finite-matrix-shape matrix-shape/rectangular-tail-spec) (extend-spec-if-missing 'matrix/prepend-column-empty-compatible-singleton :finite-matrix-transpose-shape transpose-shape/prepend-column-empty-compatible-singleton-spec) (extend-spec-if-missing 'matrix/prepend-column-preserves-compatibility :finite-matrix-transpose-shape transpose-shape/prepend-column-preserves-compatibility-spec) (support/extend-with :finite-matrix-transpose-multiply (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.transpose-multiply))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
