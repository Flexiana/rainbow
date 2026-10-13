(ns rainbow.math.linear.matrix.add-right
  "Transpose additivity and right distributivity for native matrices.

  A joint induction proves that total transpose preserves matrix/same-shape and
  commutes with matrix/add.  Row-wise action additivity then yields matrix
  multiplication distributivity in its right factor.  The only premise is the
  exact two-level shape equality required by truncating addition; ragged and
  empty matrices remain supported.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.prepend-add :as prepend-add]
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
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))
(defn- absurd [target impossible]
  (app impossible target))

(defn- transpose-additive-result [left right]
  (conjunction
   (matrix-same-shape (transpose left) (transpose right))
   (matrix-equivalent
    (transpose (matrix-addition left right))
    (matrix-addition (transpose left) (transpose right)))))

(def transpose-additive-with-shape-spec
  {:name 'matrix/transpose-additive-with-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (transpose-additive-result 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-shape
              (matrix-same-shape 'current-left 'current-right)]]
            (transpose-additive-result
             'current-left 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-shape
                    (matrix-same-shape empty 'current-right)]]
                  (transpose-additive-result empty 'current-right)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-shape (matrix-same-shape empty empty)]]
               (conjoin
                (matrix-same-shape empty empty)
                (matrix-equivalent empty empty)
                trivial trivial))
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-shape
                  (matrix-same-shape
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (transpose-additive-result
                  empty (cons-matrix 'right-row 'right-tail))
                 'current-shape)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-result (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-shape
                     (matrix-same-shape current-left 'current-right)]]
                   (transpose-additive-result
                    current-left 'current-right)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-shape
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (transpose-additive-result
                  current-left (nil-matrix))
                 'current-shape))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-shape
                   (matrix-same-shape
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-shape
                       (vector-same-shape 'left-row 'right-row)
                       tail-shape
                       (matrix-same-shape 'left-tail 'right-tail)
                       current-head-shape
                       (proposition-left
                        head-shape tail-shape 'current-shape)
                       current-tail-shape
                       (proposition-right
                        head-shape tail-shape 'current-shape)
                       tail-both
                       (app 'tail-result 'right-tail current-tail-shape)
                       transposed-tail-shape
                       (matrix-same-shape
                        (transpose 'left-tail)
                        (transpose 'right-tail))
                       transposed-tail-additive
                       (matrix-equivalent
                        (transpose
                         (matrix-addition 'left-tail 'right-tail))
                        (matrix-addition
                         (transpose 'left-tail)
                         (transpose 'right-tail)))
                       tail-transpose-shape
                       (proposition-left
                        transposed-tail-shape
                        transposed-tail-additive
                        tail-both)
                       tail-transpose-additive
                       (proposition-right
                        transposed-tail-shape
                        transposed-tail-additive
                        tail-both)
                       prepend-both
                       (app
                        (function/const*
                         'matrix/prepend-column-additive-with-shape [])
                        'left-row 'right-row
                        (transpose 'left-tail)
                        (transpose 'right-tail)
                        current-head-shape tail-transpose-shape)
                       output-shape
                       (matrix-same-shape
                        (prepend-column
                         'left-row (transpose 'left-tail))
                        (prepend-column
                         'right-row (transpose 'right-tail)))
                       prepend-additive
                       (matrix-equivalent
                        (prepend-column
                         (vector-add 'left-row 'right-row)
                         (matrix-addition
                          (transpose 'left-tail)
                          (transpose 'right-tail)))
                        (matrix-addition
                         (prepend-column
                          'left-row (transpose 'left-tail))
                         (prepend-column
                          'right-row (transpose 'right-tail))))
                       start
                       (prepend-column
                        (vector-add 'left-row 'right-row)
                        (transpose
                         (matrix-addition 'left-tail 'right-tail)))
                       middle
                       (prepend-column
                        (vector-add 'left-row 'right-row)
                        (matrix-addition
                         (transpose 'left-tail)
                         (transpose 'right-tail)))
                       finish
                       (matrix-addition
                        (prepend-column
                         'left-row (transpose 'left-tail))
                        (prepend-column
                         'right-row (transpose 'right-tail)))]
                   (conjoin
                    output-shape
                    (matrix-equivalent start finish)
                    (proposition-left
                     output-shape prepend-additive prepend-both)
                    (matrix-transitive
                     start middle finish
                     (app
                      (function/const*
                       'matrix/prepend-column-respects-matrix-equivalence [])
                      (vector-add 'left-row 'right-row)
                      (transpose
                       (matrix-addition 'left-tail 'right-tail))
                      (matrix-addition
                       (transpose 'left-tail)
                       (transpose 'right-tail))
                      tail-transpose-additive)
                     (proposition-right
                      output-shape prepend-additive prepend-both))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'shape)))})

(def transpose-preserves-same-shape-spec
  {:name 'matrix/transpose-preserves-same-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-same-shape (transpose 'left) (transpose 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (proposition-left
     (matrix-same-shape (transpose 'left) (transpose 'right))
     (matrix-equivalent
      (transpose (matrix-addition 'left 'right))
      (matrix-addition (transpose 'left) (transpose 'right)))
     (app
      (function/const* 'matrix/transpose-additive-with-shape [])
      'left 'right 'shape)))})

(def transpose-additive-spec
  {:name 'matrix/transpose-additive :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (transpose (matrix-addition 'left 'right))
     (matrix-addition (transpose 'left) (transpose 'right))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (proposition-right
     (matrix-same-shape (transpose 'left) (transpose 'right))
     (matrix-equivalent
      (transpose (matrix-addition 'left 'right))
      (matrix-addition (transpose 'left) (transpose 'right)))
     (app
      (function/const* 'matrix/transpose-additive-with-shape [])
      'left 'right 'shape)))})

(def multiply-additive-right-spec
  {:name 'matrix/multiply-additive-right :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['shape (matrix-same-shape 'right 'offset)]]
    (matrix-equivalent
     (multiply 'left (matrix-addition 'right 'offset))
     (matrix-addition
      (multiply 'left 'right)
      (multiply 'left 'offset))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['shape (matrix-same-shape 'right 'offset)]]
    (let [transpose-sum
          (transpose (matrix-addition 'right 'offset))
          sum-transposes
          (matrix-addition (transpose 'right) (transpose 'offset))
          transpose-additive
          (app (function/const* 'matrix/transpose-additive [])
               'right 'offset 'shape)
          transpose-shape
          (app (function/const* 'matrix/transpose-preserves-same-shape [])
               'right 'offset 'shape)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply
             'current-left (matrix-addition 'right 'offset))
            (matrix-addition
             (multiply 'current-left 'right)
             (multiply 'current-left 'offset))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-distributes (app motive 'tail)]]
           (let [start (vector-multiply transpose-sum 'row)
                 middle (vector-multiply sum-transposes 'row)
                 finish
                 (vector-add
                  (vector-multiply (transpose 'right) 'row)
                  (vector-multiply (transpose 'offset) 'row))]
             (conjoin
              (vector-equivalent start finish)
              (matrix-equivalent
               (multiply 'tail (matrix-addition 'right 'offset))
               (matrix-addition
                (multiply 'tail 'right)
                (multiply 'tail 'offset)))
              (vector-transitive
               start middle finish
               (app
                (function/const*
                 'matrix/vector-multiply-respects-matrix-equivalence [])
                transpose-sum sum-transposes 'row transpose-additive)
               (app
                (function/const*
                 'matrix/vector-multiply-additive-rows [])
                (transpose 'right) (transpose 'offset) 'row
                transpose-shape))
              'tail-distributes)))]
      (matrix-rec motive trivial step 'left)))})

(def definition-specs [])
(def theorem-specs
  [transpose-additive-with-shape-spec
   transpose-preserves-same-shape-spec
   transpose-additive-spec
   multiply-additive-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      prepend-add/extend-environment
      (support/extend-with :finite-matrix-add-right theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
