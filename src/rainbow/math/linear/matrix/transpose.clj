(ns rainbow.math.linear.matrix.transpose
  "Total transpose primitives for row-major finite signed matrices.

  matrix/prepend-column inserts a vector as the new first component of each
  existing column.  Its recursion is anchored to the vector: missing columns
  become singleton columns and surplus columns are dropped.  Folding that
  primitive from the bottom row upward defines matrix/transpose.  Rectangular
  matrices therefore receive ordinary transpose semantics, while ragged input
  still has deterministic total behavior.  The constructor laws form the
  reduction API for later shape, involution, and matrix-composition proofs.
  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.equivalence :as equivalence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

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
  (app (function/const* 'data/List.rec [type-level type-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level type-level])
       vector-type motive base step rows))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))

(def prepend-column-spec
  {:name 'matrix/prepend-column :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type matrix-type matrix-type)
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]]
    (let [outer-motive
          (function/lam
           [['ignored vector-type]]
           (function/arrow matrix-type matrix-type))
          outer-base
          (function/lam [['ignored-columns matrix-type]] (nil-matrix))
          outer-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['prepend-tail (function/arrow matrix-type matrix-type)]]
           (function/lam
            [['current-columns matrix-type]]
            (let [inner-motive
                  (function/lam [['ignored matrix-type]] matrix-type)
                  inner-base
                  (cons-matrix
                   (cons-vector 'head (nil-vector))
                   (app 'prepend-tail (nil-matrix)))
                  inner-step
                  (function/lam
                   [['column vector-type] ['remaining-columns matrix-type]
                    ['ignored matrix-type]]
                   (cons-matrix
                    (cons-vector 'head 'column)
                    (app 'prepend-tail 'remaining-columns)))]
              (matrix-rec inner-motive inner-base inner-step
                          'current-columns))))]
      (app (vector-rec outer-motive outer-base outer-step 'values)
           'columns)))})

(def transpose-spec
  {:name 'matrix/transpose :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type)
   :value
   (function/lam
    [['rows matrix-type]]
    (matrix-rec
     (function/lam [['ignored matrix-type]] matrix-type)
     (nil-matrix)
     (function/lam
      [['row vector-type] ['tail matrix-type] ['tail-transpose matrix-type]]
      (prepend-column 'row 'tail-transpose))
     'rows))})

(def prepend-column-empty-vector-spec
  {:name 'matrix/prepend-column-empty-vector :universes []
   :type
   (function/forall
    [['columns matrix-type]]
    (matrix-equivalent
     (prepend-column (nil-vector) 'columns)
     (nil-matrix)))
   :value
   (function/lam
    [['columns matrix-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (nil-matrix)))})

(def prepend-column-cons-empty-spec
  {:name 'matrix/prepend-column-cons-empty :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]]
    (matrix-equivalent
     (prepend-column (cons-vector 'head 'tail) (nil-matrix))
     (cons-matrix
      (cons-vector 'head (nil-vector))
      (prepend-column 'tail (nil-matrix)))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (cons-matrix
          (cons-vector 'head (nil-vector))
          (prepend-column 'tail (nil-matrix)))))})

(def prepend-column-cons-cons-spec
  {:name 'matrix/prepend-column-cons-cons :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]
     ['column vector-type] ['columns matrix-type]]
    (matrix-equivalent
     (prepend-column
      (cons-vector 'head 'tail)
      (cons-matrix 'column 'columns))
     (cons-matrix
      (cons-vector 'head 'column)
      (prepend-column 'tail 'columns))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]
     ['column vector-type] ['columns matrix-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (cons-matrix
          (cons-vector 'head 'column)
          (prepend-column 'tail 'columns))))})

(def transpose-empty-spec
  {:name 'matrix/transpose-empty :universes []
   :type
   (matrix-equivalent (transpose (nil-matrix)) (nil-matrix))
   :value
   (app (function/const* 'matrix/equivalent-reflexive []) (nil-matrix))})

(def transpose-cons-spec
  {:name 'matrix/transpose-cons :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type]]
    (matrix-equivalent
     (transpose (cons-matrix 'row 'tail))
     (prepend-column 'row (transpose 'tail))))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (prepend-column 'row (transpose 'tail))))})

(def definition-specs [prepend-column-spec transpose-spec])
(def theorem-specs
  [prepend-column-empty-vector-spec
   prepend-column-cons-empty-spec
   prepend-column-cons-cons-spec
   transpose-empty-spec
   transpose-cons-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-transpose (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.transpose))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
