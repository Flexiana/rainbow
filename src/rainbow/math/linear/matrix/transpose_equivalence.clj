(ns rainbow.math.linear.matrix.transpose-equivalence
  "Congruence laws for total native matrix transpose.

  matrix/prepend-column respects vector equivalence and matrix equivalence
  separately, then jointly by transitivity.  Structural row induction lifts
  the joint law to matrix/transpose.  Consequently transpose is well-defined
  on the quotient represented by matrix/equivalent, including the explicit
  total semantics for ragged matrices.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.equivalence-shape :as equivalence-shape]
            [rainbow.math.linear.matrix.transpose :as transpose]
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
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
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

(def prepend-column-respects-vector-equivalence-spec
  {:name 'matrix/prepend-column-respects-vector-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['columns matrix-type]
     ['same (vector-equivalent 'left 'right)]]
    (matrix-equivalent
     (prepend-column 'left 'columns)
     (prepend-column 'right 'columns)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['columns matrix-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type] ['current-columns matrix-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (matrix-equivalent
             (prepend-column 'current-left 'current-columns)
             (prepend-column 'current-right 'current-columns))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-columns matrix-type]
                   ['current-same
                    (vector-equivalent empty 'current-right)]]
                  (matrix-equivalent
                   (prepend-column empty 'current-columns)
                   (prepend-column 'current-right 'current-columns))))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              right-motive
              (function/lam
               [['current-columns matrix-type]
                ['current-same (vector-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-columns matrix-type]
                 ['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (matrix-equivalent
                  (prepend-column empty 'current-columns)
                  (prepend-column
                   (cons-vector 'right-head 'right-tail)
                   'current-columns))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-respects (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-columns matrix-type]
                    ['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (matrix-equivalent
                    (prepend-column current-left 'current-columns)
                    (prepend-column 'current-right 'current-columns))))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               right-motive
               (function/lam
                [['current-columns matrix-type]
                 ['current-same
                  (vector-equivalent current-left (nil-vector))]]
                (absurd
                 (matrix-equivalent
                  (prepend-column current-left 'current-columns)
                  (prepend-column (nil-vector) 'current-columns))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored-right (app right-motive 'right-tail)]]
                (function/lam
                 [['current-columns matrix-type]
                  ['current-same
                   (vector-equivalent
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-same
                       (proposition-left
                        (signed-equivalent 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (signed-equivalent 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)
                       columns-motive
                       (function/lam
                        [['candidate-columns matrix-type]]
                        (matrix-equivalent
                         (prepend-column current-left 'candidate-columns)
                         (prepend-column
                          (cons-vector 'right-head 'right-tail)
                          'candidate-columns)))
                       columns-base
                       (conjoin
                        (vector-equivalent
                         (cons-vector 'left-head (nil-vector))
                         (cons-vector 'right-head (nil-vector)))
                        (matrix-equivalent
                         (prepend-column 'left-tail (nil-matrix))
                         (prepend-column 'right-tail (nil-matrix)))
                        (conjoin
                         (signed-equivalent 'left-head 'right-head)
                         (vector-equivalent (nil-vector) (nil-vector))
                         head-same trivial)
                        (app 'tail-respects
                             'right-tail (nil-matrix) tail-same))
                       columns-step
                       (function/lam
                        [['column vector-type]
                         ['remaining-columns matrix-type]
                         ['ignored-columns
                          (app columns-motive 'remaining-columns)]]
                        (conjoin
                         (vector-equivalent
                          (cons-vector 'left-head 'column)
                          (cons-vector 'right-head 'column))
                         (matrix-equivalent
                          (prepend-column 'left-tail 'remaining-columns)
                          (prepend-column 'right-tail 'remaining-columns))
                         (conjoin
                          (signed-equivalent 'left-head 'right-head)
                          (vector-equivalent 'column 'column)
                          head-same
                          (app
                           (function/const*
                            'vector/equivalent-reflexive [])
                           'column))
                         (app 'tail-respects
                              'right-tail 'remaining-columns tail-same)))]
                   (matrix-rec columns-motive columns-base columns-step
                               'current-columns))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'columns 'same)))})

(def prepend-column-respects-matrix-equivalence-spec
  {:name 'matrix/prepend-column-respects-matrix-equivalence :universes []
   :type
   (function/forall
    [['values vector-type] ['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (matrix-equivalent
     (prepend-column 'values 'left)
     (prepend-column 'values 'right)))
   :value
   (function/lam
    [['values vector-type] ['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-left matrix-type] ['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (matrix-equivalent
             (prepend-column 'current-values 'current-left)
             (prepend-column 'current-values 'current-right))))
          values-base
          (function/lam
           [['current-left matrix-type] ['current-right matrix-type]
            ['current-same
             (matrix-equivalent 'current-left 'current-right)]]
           trivial)
          values-step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-respects (app values-motive 'tail)]]
           (let [current-values (cons-vector 'head 'tail)
                 left-motive
                 (function/lam
                  [['current-left matrix-type]]
                  (function/forall
                   [['current-right matrix-type]
                    ['current-same
                     (matrix-equivalent 'current-left 'current-right)]]
                   (matrix-equivalent
                    (prepend-column current-values 'current-left)
                    (prepend-column current-values 'current-right))))]
             (function/lam
              [['current-left matrix-type]]
              (matrix-rec
               left-motive
               (let [empty (nil-matrix)
                     right-motive
                     (function/lam
                      [['current-right matrix-type]]
                      (function/forall
                       [['current-same
                         (matrix-equivalent empty 'current-right)]]
                       (matrix-equivalent
                        (prepend-column current-values empty)
                        (prepend-column current-values 'current-right))))]
                 (function/lam
                  [['current-right matrix-type]]
                  (matrix-rec
                   right-motive
                   (function/lam
                    [['current-same (matrix-equivalent empty empty)]]
                    (conjoin
                     (vector-equivalent
                      (cons-vector 'head (nil-vector))
                      (cons-vector 'head (nil-vector)))
                     (matrix-equivalent
                      (prepend-column 'tail empty)
                      (prepend-column 'tail empty))
                     (app
                      (function/const* 'vector/equivalent-reflexive [])
                      (cons-vector 'head (nil-vector)))
                     (app 'tail-respects empty empty trivial)))
                   (function/lam
                    [['right-column vector-type]
                     ['right-columns matrix-type]
                     ['ignored (app right-motive 'right-columns)]]
                    (function/lam
                     [['current-same
                       (matrix-equivalent
                        empty
                        (cons-matrix 'right-column 'right-columns))]]
                     (absurd
                      (matrix-equivalent
                       (prepend-column current-values empty)
                       (prepend-column
                        current-values
                        (cons-matrix 'right-column 'right-columns)))
                      'current-same)))
                   'current-right)))
               (function/lam
                [['left-column vector-type] ['left-columns matrix-type]
                 ['ignored-left (app left-motive 'left-columns)]]
                (let [current-left
                      (cons-matrix 'left-column 'left-columns)
                      right-motive
                      (function/lam
                       [['current-right matrix-type]]
                       (function/forall
                        [['current-same
                          (matrix-equivalent current-left 'current-right)]]
                        (matrix-equivalent
                         (prepend-column current-values current-left)
                         (prepend-column current-values 'current-right))))]
                  (function/lam
                   [['current-right matrix-type]]
                   (matrix-rec
                    right-motive
                    (function/lam
                     [['current-same
                       (matrix-equivalent current-left (nil-matrix))]]
                     (absurd
                      (matrix-equivalent
                       (prepend-column current-values current-left)
                       (prepend-column current-values (nil-matrix)))
                      'current-same))
                    (function/lam
                     [['right-column vector-type]
                      ['right-columns matrix-type]
                      ['ignored-right (app right-motive 'right-columns)]]
                     (function/lam
                      [['current-same
                        (matrix-equivalent
                         current-left
                         (cons-matrix 'right-column 'right-columns))]]
                      (let [column-same
                            (proposition-left
                             (vector-equivalent
                              'left-column 'right-column)
                             (matrix-equivalent
                              'left-columns 'right-columns)
                             'current-same)
                            columns-same
                            (proposition-right
                             (vector-equivalent
                              'left-column 'right-column)
                             (matrix-equivalent
                              'left-columns 'right-columns)
                             'current-same)]
                        (conjoin
                         (vector-equivalent
                          (cons-vector 'head 'left-column)
                          (cons-vector 'head 'right-column))
                         (matrix-equivalent
                          (prepend-column 'tail 'left-columns)
                          (prepend-column 'tail 'right-columns))
                         (conjoin
                          (signed-equivalent 'head 'head)
                          (vector-equivalent
                           'left-column 'right-column)
                          (app
                           (function/const*
                            'signed/equivalent-reflexive [])
                           'head)
                          column-same)
                         (app 'tail-respects
                              'left-columns 'right-columns columns-same)))))
                    'current-right))))
               'current-left))))]
      (app (vector-rec values-motive values-base values-step 'values)
           'left 'right 'same)))})

(def prepend-column-respects-equivalence-spec
  {:name 'matrix/prepend-column-respects-equivalence :universes []
   :type
   (function/forall
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-same (vector-equivalent 'left-values 'right-values)]
     ['columns-same
      (matrix-equivalent 'left-columns 'right-columns)]]
    (matrix-equivalent
     (prepend-column 'left-values 'left-columns)
     (prepend-column 'right-values 'right-columns)))
   :value
   (function/lam
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-same (vector-equivalent 'left-values 'right-values)]
     ['columns-same
      (matrix-equivalent 'left-columns 'right-columns)]]
    (app
     (function/const* 'matrix/equivalent-transitive [])
     (prepend-column 'left-values 'left-columns)
     (prepend-column 'right-values 'left-columns)
     (prepend-column 'right-values 'right-columns)
     (app
      (function/const*
       'matrix/prepend-column-respects-vector-equivalence [])
      'left-values 'right-values 'left-columns 'values-same)
     (app
      (function/const*
       'matrix/prepend-column-respects-matrix-equivalence [])
      'right-values 'left-columns 'right-columns 'columns-same)))})

(def transpose-respects-equivalence-spec
  {:name 'matrix/transpose-respects-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (matrix-equivalent
     (matrix-transpose 'left)
     (matrix-transpose 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (matrix-equivalent
             (matrix-transpose 'current-left)
             (matrix-transpose 'current-right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (matrix-equivalent
                   (matrix-transpose empty)
                   (matrix-transpose 'current-right))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (matrix-equivalent
                  (matrix-transpose empty)
                  (matrix-transpose
                   (cons-matrix 'right-row 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-respects (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (matrix-equivalent
                    (matrix-transpose current-left)
                    (matrix-transpose 'current-right))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (matrix-transpose current-left)
                  (matrix-transpose (nil-matrix)))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [row-same
                       (proposition-left
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)]
                   (app
                    (function/const*
                     'matrix/prepend-column-respects-equivalence [])
                    'left-row 'right-row
                    (matrix-transpose 'left-tail)
                    (matrix-transpose 'right-tail)
                    row-same
                    (app 'tail-respects 'right-tail tail-same)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def definition-specs [])
(def theorem-specs
  [prepend-column-respects-vector-equivalence-spec
   prepend-column-respects-matrix-equivalence-spec
   prepend-column-respects-equivalence-spec
   transpose-respects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'matrix/equivalent-transitive :finite-matrix-equivalence-shape equivalence-shape/matrix-equivalent-transitive-spec) (support/extend-with :finite-matrix-transpose-equivalence theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.transpose-equivalence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
