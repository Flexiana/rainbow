(ns rainbow.math.linear.matrix.transpose-multiply-reverse
  "Transpose reverses native matrix multiplication at positive width.

  A rectangular matrix with an explicitly nonempty first row is recovered by
  double transpose.  Mapping its action over columns is therefore equivalent
  to multiplying those columns by its transpose; composing that fact with the
  nonempty-left transpose/product bridge yields

      transpose (B*C) ~ transpose C * transpose B.

  No premise on C is required.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.transpose-involution-positive :as involution]
            [rainbow.math.linear.matrix.transpose-multiply :as transpose-product]
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
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
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
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- vector-symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))

(def column-action-to-transpose-product-spec
  {:name 'matrix/column-action-to-transpose-product :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['columns matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (matrix-equivalent
     (column-action
      (cons-matrix (cons-vector 'head 'row-tail) 'tail)
      'columns)
     (multiply
      'columns
      (transpose
       (cons-matrix (cons-vector 'head 'row-tail) 'tail)))))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['columns matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (let [rows (cons-matrix (cons-vector 'head 'row-tail) 'tail)
          twice (transpose (transpose rows))
          involutive
          (app
           (function/const*
            'matrix/transpose-involutive-nonempty-width [])
           'head 'row-tail 'tail 'rows-rectangular)
          motive
          (function/lam
           [['current-columns matrix-type]]
           (matrix-equivalent
            (column-action rows 'current-columns)
            (multiply 'current-columns (transpose rows))))
          step
          (function/lam
           [['column vector-type] ['remaining-columns matrix-type]
            ['tail-same (app motive 'remaining-columns)]]
           (let [twice-to-rows
                 (app
                  (function/const*
                   'matrix/vector-multiply-respects-matrix-equivalence [])
                  twice rows 'column involutive)
                 rows-to-twice
                 (vector-symmetric
                  (vector-multiply twice 'column)
                  (vector-multiply rows 'column)
                  twice-to-rows)]
             (conjoin
              (vector-equivalent
               (vector-multiply rows 'column)
               (vector-multiply twice 'column))
              (matrix-equivalent
               (column-action rows 'remaining-columns)
               (multiply 'remaining-columns (transpose rows)))
              rows-to-twice 'tail-same)))]
      (matrix-rec motive trivial step 'columns)))})

(def transpose-multiply-reverses-positive-width-spec
  {:name 'matrix/transpose-multiply-reverses-positive-width :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['right matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (matrix-equivalent
     (transpose
      (multiply
       (cons-matrix (cons-vector 'head 'row-tail) 'tail)
       'right))
     (multiply
      (transpose 'right)
      (transpose
       (cons-matrix (cons-vector 'head 'row-tail) 'tail)))))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['right matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (let [rows (cons-matrix (cons-vector 'head 'row-tail) 'tail)
          columns (transpose 'right)
          column-images (column-action rows columns)
          reversed (multiply columns (transpose rows))]
      (matrix-transitive
       (transpose (multiply rows 'right))
       column-images reversed
       (app
        (function/const* 'matrix/transpose-multiply-nonempty-left [])
        (cons-vector 'head 'row-tail) 'tail 'right)
       (app
        (function/const* 'matrix/column-action-to-transpose-product [])
        'head 'row-tail 'tail columns 'rows-rectangular))))})

(def definition-specs [])
(def theorem-specs
  [column-action-to-transpose-product-spec
   transpose-multiply-reverses-positive-width-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-involution-positive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-transpose-multiply-reverse theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.transpose-multiply-reverse))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
