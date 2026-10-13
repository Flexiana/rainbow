(ns rainbow.math.linear.matrix.multiply-shape
  "Unconditional output-shape laws for native matrix multiplication.

  matrix/vector-multiply always returns one component per matrix row, so its
  result has matrix/column-shape.  Lifting that fact through matrix/multiply
  proves that product row count matches the left matrix, every output row is
  compatible with any other row image, and every product is rectangular—even
  when the total ragged/truncating semantics is used.  Native and axiom-free on
  D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.linear :as matrix-linear]
            [rainbow.math.linear.matrix.multiply :as multiply]
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
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- matrix-multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def vector-multiply-column-shape-spec
  {:name 'matrix/vector-multiply-column-shape :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]]
    (same-shape
     (vector-multiply 'rows 'values)
     (column-shape 'rows)))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (same-shape
            (vector-multiply 'current-rows 'values)
            (column-shape 'current-rows)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (signed-equivalent signed-zero signed-zero)
            (same-shape
             (vector-multiply 'tail 'values)
             (column-shape 'tail))
            (app (function/const* 'signed/equivalent-reflexive [])
                 signed-zero)
            'tail-shape))]
      (matrix-rec motive trivial step 'rows)))})

(def multiply-left-column-shape-spec
  {:name 'matrix/multiply-left-column-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]]
    (same-shape
     (column-shape (matrix-multiply 'left 'right))
     (column-shape 'left)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (let [motive
          (function/lam
           [['current-left matrix-type]]
           (same-shape
            (column-shape (matrix-multiply 'current-left 'right))
            (column-shape 'current-left)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (signed-equivalent signed-zero signed-zero)
            (same-shape
             (column-shape (matrix-multiply 'tail 'right))
             (column-shape 'tail))
            (app (function/const* 'signed/equivalent-reflexive [])
                 signed-zero)
            'tail-shape))]
      (matrix-rec motive trivial step 'left)))})

(def multiply-compatible-with-row-image-spec
  {:name 'matrix/multiply-compatible-with-row-image :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['reference vector-type]]
    (compatible
     (matrix-multiply 'left 'right)
     (vector-multiply (transpose 'right) 'reference)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['reference vector-type]]
    (let [motive
          (function/lam
           [['current-left matrix-type]]
           (compatible
            (matrix-multiply 'current-left 'right)
            (vector-multiply (transpose 'right) 'reference)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-compatible (app motive 'tail)]]
           (conjoin
            (same-shape
             (vector-multiply (transpose 'right) 'row)
             (vector-multiply (transpose 'right) 'reference))
            (compatible
             (matrix-multiply 'tail 'right)
             (vector-multiply (transpose 'right) 'reference))
            (app
             (function/const*
              'matrix/vector-multiply-output-shape [])
             (transpose 'right) 'row 'reference)
            'tail-compatible))]
      (matrix-rec motive trivial step 'left)))})

(def multiply-rectangular-spec
  {:name 'matrix/multiply-rectangular :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]]
    (rectangular (matrix-multiply 'left 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (let [motive
          (function/lam
           [['current-left matrix-type]]
           (rectangular (matrix-multiply 'current-left 'right)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['ignored (app motive 'tail)]]
           (app
            (function/const*
             'matrix/multiply-compatible-with-row-image [])
            'tail 'right 'row))]
      (matrix-rec motive trivial step 'left)))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-column-shape-spec
   multiply-left-column-shape-spec
   multiply-compatible-with-row-image-spec
   multiply-rectangular-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      multiply/extend-environment
      (extend-spec-if-missing
       'matrix/vector-multiply-output-shape :finite-matrix-linear
       matrix-linear/vector-multiply-output-shape-spec)
      (extend-spec-if-missing
       'matrix/column-shape :finite-matrix-transpose-shape
       transpose-shape/column-shape-spec)
      (extend-spec-if-missing
       'matrix/compatible :finite-matrix-shape
       matrix-shape/compatible-spec)
      (extend-spec-if-missing
       'matrix/rectangular :finite-matrix-shape
       matrix-shape/rectangular-spec)
      (support/extend-with :finite-matrix-multiply-shape theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
