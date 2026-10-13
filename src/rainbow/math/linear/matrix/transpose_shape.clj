(ns rainbow.math.linear.matrix.transpose-shape
  "Rectangularity laws for total native matrix transpose.

  matrix/column-shape maps each row of a matrix to one signed zero, yielding a
  vector whose length is the matrix row count.  Thus vector/same-shape between
  an inserted vector and column-shape records the exact width precondition for
  matrix/prepend-column.  Structural laws show insertion preserves
  compatibility and rectangularity under that certificate, and finally that
  transpose sends every rectangular matrix to a rectangular matrix.  Native
  and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
            [rainbow.math.linear.matrix.transpose-equivalence :as transpose-equivalence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-cancellation :as vector-shape]))

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
(defn- list-map [from to mapping values]
  (app (function/const* 'list/map [type-level type-level])
       from to mapping values))
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
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- matrix-transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def column-shape-spec
  {:name 'matrix/column-shape :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type)
   :value
   (function/lam
    [['rows matrix-type]]
    (list-map
     vector-type signed
     (function/lam [['ignored vector-type]] signed-zero)
     'rows))})

(def prepend-column-output-shape-spec
  {:name 'matrix/prepend-column-output-shape :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]]
    (same-shape
     (column-shape (prepend-column 'values 'columns))
     'values))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]]
            (same-shape
             (column-shape
              (prepend-column 'current-values 'current-columns))
             'current-values)))
          values-base
          (function/lam [['current-columns matrix-type]] trivial)
          values-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-shape (app values-motive 'tail)]]
           (function/lam
            [['current-columns matrix-type]]
            (let [columns-motive
                  (function/lam
                   [['candidate-columns matrix-type]]
                   (same-shape
                    (column-shape
                     (prepend-column
                      (cons-vector 'head 'tail) 'candidate-columns))
                    (cons-vector 'head 'tail)))
                  columns-base
                  (conjoin
                   (signed-equivalent signed-zero signed-zero)
                   (same-shape
                    (column-shape
                     (prepend-column 'tail (nil-matrix)))
                    'tail)
                   (app (function/const* 'signed/equivalent-reflexive [])
                        signed-zero)
                   (app 'tail-shape (nil-matrix)))
                  columns-step
                  (function/lam
                   [['column vector-type] ['remaining-columns matrix-type]
                    ['ignored (app columns-motive 'remaining-columns)]]
                   (conjoin
                    (signed-equivalent signed-zero signed-zero)
                    (same-shape
                     (column-shape
                      (prepend-column 'tail 'remaining-columns))
                     'tail)
                    (app (function/const* 'signed/equivalent-reflexive [])
                         signed-zero)
                    (app 'tail-shape 'remaining-columns)))]
              (matrix-rec columns-motive columns-base columns-step
                          'current-columns))))]
      (app (vector-rec values-motive values-base values-step 'values)
           'columns)))})

(def prepend-column-empty-compatible-singleton-spec
  {:name 'matrix/prepend-column-empty-compatible-singleton :universes []
   :type
   (function/forall
    [['values vector-type] ['reference signed]]
    (compatible
     (prepend-column 'values (nil-matrix))
     (cons-vector 'reference (nil-vector))))
   :value
   (function/lam
    [['values vector-type] ['reference signed]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (compatible
            (prepend-column 'current (nil-matrix))
            (cons-vector 'reference (nil-vector))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-compatible (app motive 'tail)]]
           (conjoin
            (same-shape
             (cons-vector 'head (nil-vector))
             (cons-vector 'reference (nil-vector)))
            (compatible
             (prepend-column 'tail (nil-matrix))
             (cons-vector 'reference (nil-vector)))
            (conjoin
             (signed-equivalent signed-zero signed-zero)
             (same-shape (nil-vector) (nil-vector))
             (app (function/const* 'signed/equivalent-reflexive [])
                  signed-zero)
             trivial)
            'tail-compatible))]
      (vector-rec motive trivial step 'values)))})

(def prepend-column-empty-rectangular-spec
  {:name 'matrix/prepend-column-empty-rectangular :universes []
   :type
   (function/forall
    [['values vector-type]]
    (rectangular (prepend-column 'values (nil-matrix))))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (rectangular
            (prepend-column 'current (nil-matrix))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['ignored (app motive 'tail)]]
           (app
            (function/const*
             'matrix/prepend-column-empty-compatible-singleton [])
            'tail 'head))]
      (vector-rec motive trivial step 'values)))})

(def prepend-column-preserves-compatibility-spec
  {:name 'matrix/prepend-column-preserves-compatibility :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]
     ['reference-head signed] ['reference-column vector-type]
     ['width (same-shape 'values (column-shape 'columns))]
     ['columns-compatible (compatible 'columns 'reference-column)]]
    (compatible
     (prepend-column 'values 'columns)
     (cons-vector 'reference-head 'reference-column)))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]
     ['reference-head signed] ['reference-column vector-type]
     ['width (same-shape 'values (column-shape 'columns))]
     ['columns-compatible (compatible 'columns 'reference-column)]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]
             ['current-reference-head signed]
             ['current-reference-column vector-type]
             ['current-width
              (same-shape
               'current-values (column-shape 'current-columns))]
             ['current-compatible
              (compatible 'current-columns 'current-reference-column)]]
            (compatible
             (prepend-column 'current-values 'current-columns)
             (cons-vector
              'current-reference-head 'current-reference-column))))
          values-base
          (let [empty (nil-vector)
                columns-motive
                (function/lam
                 [['current-columns matrix-type]]
                 (function/forall
                  [['current-reference-head signed]
                   ['current-reference-column vector-type]
                   ['current-width
                    (same-shape empty (column-shape 'current-columns))]
                   ['current-compatible
                    (compatible
                     'current-columns 'current-reference-column)]]
                  (compatible
                   (prepend-column empty 'current-columns)
                   (cons-vector
                    'current-reference-head 'current-reference-column))))]
            (function/lam
             [['current-columns matrix-type]]
             (matrix-rec
              columns-motive
              (function/lam
               [['current-reference-head signed]
                ['current-reference-column vector-type]
                ['current-width
                 (same-shape empty (column-shape (nil-matrix)))]
                ['current-compatible
                 (compatible (nil-matrix) 'current-reference-column)]]
               trivial)
              (function/lam
               [['column vector-type] ['remaining-columns matrix-type]
                ['ignored (app columns-motive 'remaining-columns)]]
               (function/lam
                [['current-reference-head signed]
                 ['current-reference-column vector-type]
                 ['current-width
                  (same-shape
                   empty
                   (column-shape
                    (cons-matrix 'column 'remaining-columns)))]
                 ['current-compatible
                  (compatible
                   (cons-matrix 'column 'remaining-columns)
                   'current-reference-column)]]
                (absurd
                 (compatible
                  (prepend-column
                   empty (cons-matrix 'column 'remaining-columns))
                  (cons-vector
                   'current-reference-head 'current-reference-column))
                 'current-width)))
              'current-columns)))
          values-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-preserves (app values-motive 'tail)]]
           (let [current-values (cons-vector 'head 'tail)
                 columns-motive
                 (function/lam
                  [['current-columns matrix-type]]
                  (function/forall
                   [['current-reference-head signed]
                    ['current-reference-column vector-type]
                    ['current-width
                     (same-shape
                      current-values (column-shape 'current-columns))]
                    ['current-compatible
                     (compatible
                      'current-columns 'current-reference-column)]]
                   (compatible
                    (prepend-column current-values 'current-columns)
                    (cons-vector
                     'current-reference-head 'current-reference-column))))]
             (function/lam
              [['current-columns matrix-type]]
              (matrix-rec
               columns-motive
               (function/lam
                [['current-reference-head signed]
                 ['current-reference-column vector-type]
                 ['current-width
                  (same-shape current-values
                              (column-shape (nil-matrix)))]
                 ['current-compatible
                  (compatible (nil-matrix) 'current-reference-column)]]
                (absurd
                 (compatible
                  (prepend-column current-values (nil-matrix))
                  (cons-vector
                   'current-reference-head 'current-reference-column))
                 'current-width))
               (function/lam
                [['column vector-type] ['remaining-columns matrix-type]
                 ['ignored (app columns-motive 'remaining-columns)]]
                (function/lam
                 [['current-reference-head signed]
                  ['current-reference-column vector-type]
                  ['current-width
                   (same-shape
                    current-values
                    (column-shape
                     (cons-matrix 'column 'remaining-columns)))]
                  ['current-compatible
                   (compatible
                    (cons-matrix 'column 'remaining-columns)
                    'current-reference-column)]]
                 (let [tail-width
                       (proposition-right
                        (signed-equivalent signed-zero signed-zero)
                        (same-shape
                         'tail (column-shape 'remaining-columns))
                        'current-width)
                       column-shape-proof
                       (proposition-left
                        (same-shape 'column 'current-reference-column)
                        (compatible
                         'remaining-columns 'current-reference-column)
                        'current-compatible)
                       remaining-compatible
                       (proposition-right
                        (same-shape 'column 'current-reference-column)
                        (compatible
                         'remaining-columns 'current-reference-column)
                        'current-compatible)
                       output-head-shape
                       (conjoin
                        (signed-equivalent signed-zero signed-zero)
                        (same-shape 'column 'current-reference-column)
                        (app
                         (function/const* 'signed/equivalent-reflexive [])
                         signed-zero)
                        column-shape-proof)
                       output-tail-compatible
                       (app 'tail-preserves
                            'remaining-columns
                            'current-reference-head
                            'current-reference-column
                            tail-width remaining-compatible)]
                   (conjoin
                    (same-shape
                     (cons-vector 'head 'column)
                     (cons-vector
                      'current-reference-head 'current-reference-column))
                    (compatible
                     (prepend-column 'tail 'remaining-columns)
                     (cons-vector
                      'current-reference-head 'current-reference-column))
                    output-head-shape output-tail-compatible))))
               'current-columns))))]
      (app (vector-rec values-motive values-base values-step 'values)
           'columns 'reference-head 'reference-column
           'width 'columns-compatible)))})

(def prepend-column-preserves-rectangularity-spec
  {:name 'matrix/prepend-column-preserves-rectangularity :universes []
   :type
   (function/forall
    [['values vector-type] ['columns matrix-type]
     ['width (same-shape 'values (column-shape 'columns))]
     ['columns-rectangular (rectangular 'columns)]]
    (rectangular (prepend-column 'values 'columns)))
   :value
   (function/lam
    [['values vector-type] ['columns matrix-type]
     ['width (same-shape 'values (column-shape 'columns))]
     ['columns-rectangular (rectangular 'columns)]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]
             ['current-width
              (same-shape
               'current-values (column-shape 'current-columns))]
             ['current-rectangular (rectangular 'current-columns)]]
            (rectangular
             (prepend-column 'current-values 'current-columns))))
          values-base
          (let [empty (nil-vector)
                columns-motive
                (function/lam
                 [['current-columns matrix-type]]
                 (function/forall
                  [['current-width
                    (same-shape empty (column-shape 'current-columns))]
                   ['current-rectangular (rectangular 'current-columns)]]
                  (rectangular
                   (prepend-column empty 'current-columns))))]
            (function/lam
             [['current-columns matrix-type]]
             (matrix-rec
              columns-motive
              (function/lam
               [['current-width
                 (same-shape empty (column-shape (nil-matrix)))]
                ['current-rectangular (rectangular (nil-matrix))]]
               trivial)
              (function/lam
               [['column vector-type] ['remaining-columns matrix-type]
                ['ignored (app columns-motive 'remaining-columns)]]
               (function/lam
                [['current-width
                  (same-shape
                   empty
                   (column-shape
                    (cons-matrix 'column 'remaining-columns)))]
                 ['current-rectangular
                  (rectangular
                   (cons-matrix 'column 'remaining-columns))]]
                (absurd
                 (rectangular
                  (prepend-column
                   empty (cons-matrix 'column 'remaining-columns)))
                 'current-width)))
              'current-columns)))
          values-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['ignored (app values-motive 'tail)]]
           (let [current-values (cons-vector 'head 'tail)
                 columns-motive
                 (function/lam
                  [['current-columns matrix-type]]
                  (function/forall
                   [['current-width
                     (same-shape
                      current-values (column-shape 'current-columns))]
                    ['current-rectangular (rectangular 'current-columns)]]
                   (rectangular
                    (prepend-column current-values 'current-columns))))]
             (function/lam
              [['current-columns matrix-type]]
              (matrix-rec
               columns-motive
               (function/lam
                [['current-width
                  (same-shape current-values
                              (column-shape (nil-matrix)))]
                 ['current-rectangular (rectangular (nil-matrix))]]
                (absurd
                 (rectangular
                  (prepend-column current-values (nil-matrix)))
                 'current-width))
               (function/lam
                [['column vector-type] ['remaining-columns matrix-type]
                 ['ignored-columns
                  (app columns-motive 'remaining-columns)]]
                (function/lam
                 [['current-width
                   (same-shape
                    current-values
                    (column-shape
                     (cons-matrix 'column 'remaining-columns)))]
                  ['current-rectangular
                   (rectangular
                    (cons-matrix 'column 'remaining-columns))]]
                 (let [tail-width
                       (proposition-right
                        (signed-equivalent signed-zero signed-zero)
                        (same-shape
                         'tail (column-shape 'remaining-columns))
                        'current-width)]
                   (app
                    (function/const*
                     'matrix/prepend-column-preserves-compatibility [])
                    'tail 'remaining-columns 'head 'column
                    tail-width 'current-rectangular))))
               'current-columns))))]
      (app (vector-rec values-motive values-base values-step 'values)
           'columns 'width 'columns-rectangular)))})

(def transpose-cons-preserves-rectangularity-spec
  {:name 'matrix/transpose-cons-preserves-rectangularity :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type]
     ['rows-rectangular (rectangular (cons-matrix 'row 'tail))]
     ['tail-transpose-rectangular
      (rectangular (matrix-transpose 'tail))]]
    (rectangular
     (matrix-transpose (cons-matrix 'row 'tail))))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type]
     ['rows-rectangular (rectangular (cons-matrix 'row 'tail))]
     ['tail-transpose-rectangular
      (rectangular (matrix-transpose 'tail))]]
    (let [tail-motive
          (function/lam
           [['current-tail matrix-type]]
           (function/forall
            [['current-row vector-type]
             ['current-rectangular
              (rectangular
               (cons-matrix 'current-row 'current-tail))]
             ['current-tail-transpose-rectangular
              (rectangular (matrix-transpose 'current-tail))]]
            (rectangular
             (matrix-transpose
              (cons-matrix 'current-row 'current-tail)))))
          tail-base
          (function/lam
           [['current-row vector-type]
            ['current-rectangular
             (rectangular
              (cons-matrix 'current-row (nil-matrix)))]
            ['current-tail-transpose-rectangular
             (rectangular (matrix-transpose (nil-matrix)))]]
           (app
            (function/const*
             'matrix/prepend-column-empty-rectangular [])
            'current-row))
          tail-step
          (function/lam
           [['second vector-type] ['rest matrix-type]
            ['ignored (app tail-motive 'rest)]]
           (function/lam
            [['current-row vector-type]
             ['current-rectangular
              (rectangular
               (cons-matrix
                'current-row (cons-matrix 'second 'rest)))]
             ['current-tail-transpose-rectangular
              (rectangular
               (matrix-transpose (cons-matrix 'second 'rest)))]]
            (let [current-tail (cons-matrix 'second 'rest)
                  second-row-shape
                  (app
                   (function/const* 'matrix/compatible-head-shape [])
                   'second 'rest 'current-row 'current-rectangular)
                  row-second-shape
                  (app (function/const* 'vector/same-shape-symmetric [])
                       'second 'current-row second-row-shape)
                  transpose-tail-output-shape
                  (app
                   (function/const*
                    'matrix/prepend-column-output-shape [])
                   'second (matrix-transpose 'rest))
                  second-columns-shape
                  (app (function/const* 'vector/same-shape-symmetric [])
                       (column-shape (matrix-transpose current-tail))
                       'second transpose-tail-output-shape)
                  row-columns-shape
                  (app (function/const* 'vector/same-shape-transitive [])
                       'current-row 'second
                       (column-shape (matrix-transpose current-tail))
                       row-second-shape second-columns-shape)]
              (app
               (function/const*
                'matrix/prepend-column-preserves-rectangularity [])
               'current-row (matrix-transpose current-tail)
               row-columns-shape
               'current-tail-transpose-rectangular))))]
      (app (matrix-rec tail-motive tail-base tail-step 'tail)
           'row 'rows-rectangular 'tail-transpose-rectangular)))})

(def transpose-preserves-rectangularity-spec
  {:name 'matrix/transpose-preserves-rectangularity :universes []
   :type
   (function/forall
    [['rows matrix-type] ['rows-rectangular (rectangular 'rows)]]
    (rectangular (matrix-transpose 'rows)))
   :value
   (function/lam
    [['rows matrix-type] ['rows-rectangular (rectangular 'rows)]]
    (let [rows-motive
          (function/lam
           [['current-rows matrix-type]]
           (function/arrow
            (rectangular 'current-rows)
            (rectangular (matrix-transpose 'current-rows))))
          rows-step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-preserves (app rows-motive 'tail)]]
           (function/lam
            [['current-rectangular
              (rectangular (cons-matrix 'row 'tail))]]
            (let [tail-rectangular
                  (app (function/const* 'matrix/rectangular-tail [])
                       'row 'tail 'current-rectangular)
                  transposed-tail-rectangular
                  (app 'tail-preserves tail-rectangular)]
              (app
               (function/const*
                'matrix/transpose-cons-preserves-rectangularity [])
               'row 'tail 'current-rectangular
               transposed-tail-rectangular))))]
      (app (matrix-rec rows-motive
                       (function/lam
                        [['empty-rectangular
                          (rectangular (nil-matrix))]]
                        trivial)
                       rows-step 'rows)
           'rows-rectangular)))})

(def definition-specs [column-shape-spec])
(def theorem-specs
  [prepend-column-output-shape-spec
   prepend-column-empty-compatible-singleton-spec
   prepend-column-empty-rectangular-spec
   prepend-column-preserves-compatibility-spec
   prepend-column-preserves-rectangularity-spec
   transpose-cons-preserves-rectangularity-spec
   transpose-preserves-rectangularity-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      transpose-equivalence/extend-environment
      (extend-spec-if-missing
       'vector/same-shape :vector-shape-cancellation
       vector-shape/same-shape-spec)
      (extend-spec-if-missing
       'vector/same-shape-symmetric :vector-shape-cancellation
       vector-shape/same-shape-symmetric-spec)
      (extend-spec-if-missing
       'vector/same-shape-transitive :vector-shape-cancellation
       vector-shape/same-shape-transitive-spec)
      (extend-spec-if-missing
       'matrix/compatible :finite-matrix-shape
       matrix-shape/compatible-spec)
      (extend-spec-if-missing
       'matrix/rectangular :finite-matrix-shape
       matrix-shape/rectangular-spec)
      (extend-spec-if-missing
       'matrix/compatible-head-shape :finite-matrix-shape
       matrix-shape/compatible-head-shape-spec)
      (extend-spec-if-missing
       'matrix/compatible-transport :finite-matrix-shape
       matrix-shape/compatible-transport-spec)
      (extend-spec-if-missing
       'matrix/rectangular-tail :finite-matrix-shape
       matrix-shape/rectangular-tail-spec)
      (support/extend-with :finite-matrix-transpose-shape
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
