(ns rainbow.math.linear.matrix.prepend-add
  "Shape-safe additivity of total column insertion.

  Under matching vector and matrix shapes, matrix/prepend-column preserves the
  resulting matrix shape and distributes over vector/matrix addition.  A joint
  theorem shares the required four-list induction; public projections expose
  the shape and equivalence facts separately.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.add-shape :as add-shape]
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
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
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
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(defn- prepend-additive-result
  [left-values right-values left-columns right-columns]
  (conjunction
   (matrix-same-shape
    (prepend-column left-values left-columns)
    (prepend-column right-values right-columns))
   (matrix-equivalent
    (prepend-column
     (vector-add left-values right-values)
     (matrix-addition left-columns right-columns))
    (matrix-addition
     (prepend-column left-values left-columns)
     (prepend-column right-values right-columns)))))

(def prepend-column-additive-with-shape-spec
  {:name 'matrix/prepend-column-additive-with-shape :universes []
   :type
   (function/forall
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (prepend-additive-result
     'left-values 'right-values 'left-columns 'right-columns))
   :value
   (function/lam
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (let [values-motive
          (function/lam
           [['current-left-values vector-type]]
           (function/forall
            [['current-right-values vector-type]
             ['current-left-columns matrix-type]
             ['current-right-columns matrix-type]
             ['current-values-shape
              (vector-same-shape
               'current-left-values 'current-right-values)]
             ['current-columns-shape
              (matrix-same-shape
               'current-left-columns 'current-right-columns)]]
            (prepend-additive-result
             'current-left-values 'current-right-values
             'current-left-columns 'current-right-columns)))
          values-base
          (let [empty-values (nil-vector)
                right-values-motive
                (function/lam
                 [['current-right-values vector-type]]
                 (function/forall
                  [['current-left-columns matrix-type]
                   ['current-right-columns matrix-type]
                   ['current-values-shape
                    (vector-same-shape
                     empty-values 'current-right-values)]
                   ['current-columns-shape
                    (matrix-same-shape
                     'current-left-columns 'current-right-columns)]]
                  (prepend-additive-result
                   empty-values 'current-right-values
                   'current-left-columns 'current-right-columns)))]
            (function/lam
             [['current-right-values vector-type]]
             (vector-rec
              right-values-motive
              (function/lam
               [['current-left-columns matrix-type]
                ['current-right-columns matrix-type]
                ['current-values-shape
                 (vector-same-shape empty-values empty-values)]
                ['current-columns-shape
                 (matrix-same-shape
                  'current-left-columns 'current-right-columns)]]
               (conjoin
                (matrix-same-shape (nil-matrix) (nil-matrix))
                (matrix-equivalent (nil-matrix) (nil-matrix))
                trivial trivial))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-values-motive 'right-tail)]]
               (function/lam
                [['current-left-columns matrix-type]
                 ['current-right-columns matrix-type]
                 ['current-values-shape
                  (vector-same-shape
                   empty-values
                   (cons-vector 'right-head 'right-tail))]
                 ['current-columns-shape
                  (matrix-same-shape
                   'current-left-columns 'current-right-columns)]]
                (absurd
                 (prepend-additive-result
                  empty-values (cons-vector 'right-head 'right-tail)
                  'current-left-columns 'current-right-columns)
                 'current-values-shape)))
              'current-right-values)))
          values-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-result (app values-motive 'left-tail)]]
           (let [current-left-values
                 (cons-vector 'left-head 'left-tail)
                 right-values-motive
                 (function/lam
                  [['current-right-values vector-type]]
                  (function/forall
                   [['current-left-columns matrix-type]
                    ['current-right-columns matrix-type]
                    ['current-values-shape
                     (vector-same-shape
                      current-left-values 'current-right-values)]
                    ['current-columns-shape
                     (matrix-same-shape
                      'current-left-columns 'current-right-columns)]]
                   (prepend-additive-result
                    current-left-values 'current-right-values
                    'current-left-columns 'current-right-columns)))]
             (function/lam
              [['current-right-values vector-type]]
              (vector-rec
               right-values-motive
               (function/lam
                [['current-left-columns matrix-type]
                 ['current-right-columns matrix-type]
                 ['current-values-shape
                  (vector-same-shape
                   current-left-values (nil-vector))]
                 ['current-columns-shape
                  (matrix-same-shape
                   'current-left-columns 'current-right-columns)]]
                (absurd
                 (prepend-additive-result
                  current-left-values (nil-vector)
                  'current-left-columns 'current-right-columns)
                 'current-values-shape))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored-values
                  (app right-values-motive 'right-tail)]]
                (let [current-right-values
                      (cons-vector 'right-head 'right-tail)
                      values-head-shape
                      (signed-equivalent signed-zero signed-zero)
                      values-tail-shape
                      (vector-same-shape 'left-tail 'right-tail)]
                  (function/lam
                   [['current-left-columns matrix-type]
                    ['current-right-columns matrix-type]
                    ['current-values-shape
                     (vector-same-shape
                      current-left-values current-right-values)]
                    ['current-columns-shape
                     (matrix-same-shape
                      'current-left-columns 'current-right-columns)]]
                   (let [tail-values-shape
                         (proposition-right
                          values-head-shape values-tail-shape
                          'current-values-shape)
                         left-columns-motive
                         (function/lam
                          [['candidate-left-columns matrix-type]]
                          (function/forall
                           [['candidate-right-columns matrix-type]
                            ['candidate-columns-shape
                             (matrix-same-shape
                              'candidate-left-columns
                              'candidate-right-columns)]]
                           (prepend-additive-result
                            current-left-values current-right-values
                            'candidate-left-columns
                            'candidate-right-columns)))
                         left-columns-base
                         (let [empty-columns (nil-matrix)
                               right-columns-motive
                               (function/lam
                                [['candidate-right-columns matrix-type]]
                                (function/forall
                                 [['candidate-columns-shape
                                   (matrix-same-shape
                                    empty-columns
                                    'candidate-right-columns)]]
                                 (prepend-additive-result
                                  current-left-values current-right-values
                                  empty-columns
                                  'candidate-right-columns)))]
                           (function/lam
                            [['candidate-right-columns matrix-type]]
                            (matrix-rec
                             right-columns-motive
                             (function/lam
                              [['candidate-columns-shape
                                (matrix-same-shape
                                 empty-columns empty-columns)]]
                              (let [left-singleton
                                    (cons-vector
                                     'left-head (nil-vector))
                                    right-singleton
                                    (cons-vector
                                     'right-head (nil-vector))
                                    sum-singleton
                                    (cons-vector
                                     (signed-add 'left-head 'right-head)
                                     (nil-vector))
                                    tail-both
                                    (app 'tail-result
                                         'right-tail
                                         empty-columns empty-columns
                                         tail-values-shape trivial)
                                    output-head-shape
                                    (conjoin
                                     values-head-shape
                                     (vector-same-shape
                                      (nil-vector) (nil-vector))
                                     (app
                                      (function/const*
                                       'signed/equivalent-reflexive [])
                                      signed-zero)
                                     trivial)
                                    output-tail-shape
                                    (proposition-left
                                     (matrix-same-shape
                                      (prepend-column
                                       'left-tail empty-columns)
                                      (prepend-column
                                       'right-tail empty-columns))
                                     (matrix-equivalent
                                      (prepend-column
                                       (vector-add 'left-tail 'right-tail)
                                       (matrix-addition
                                        empty-columns empty-columns))
                                      (matrix-addition
                                       (prepend-column
                                        'left-tail empty-columns)
                                       (prepend-column
                                        'right-tail empty-columns)))
                                     tail-both)
                                    output-tail-equivalent
                                    (proposition-right
                                     (matrix-same-shape
                                      (prepend-column
                                       'left-tail empty-columns)
                                      (prepend-column
                                       'right-tail empty-columns))
                                     (matrix-equivalent
                                      (prepend-column
                                       (vector-add 'left-tail 'right-tail)
                                       (matrix-addition
                                        empty-columns empty-columns))
                                      (matrix-addition
                                       (prepend-column
                                        'left-tail empty-columns)
                                       (prepend-column
                                        'right-tail empty-columns)))
                                     tail-both)]
                                (conjoin
                                 (matrix-same-shape
                                  (prepend-column
                                   current-left-values empty-columns)
                                  (prepend-column
                                   current-right-values empty-columns))
                                 (matrix-equivalent
                                  (prepend-column
                                   (vector-add
                                    current-left-values
                                    current-right-values)
                                   (matrix-addition
                                    empty-columns empty-columns))
                                  (matrix-addition
                                   (prepend-column
                                    current-left-values empty-columns)
                                   (prepend-column
                                    current-right-values empty-columns)))
                                 (conjoin
                                  (vector-same-shape
                                   left-singleton right-singleton)
                                  (matrix-same-shape
                                   (prepend-column
                                    'left-tail empty-columns)
                                   (prepend-column
                                    'right-tail empty-columns))
                                  output-head-shape output-tail-shape)
                                 (conjoin
                                  (vector-equivalent
                                   sum-singleton sum-singleton)
                                  (matrix-equivalent
                                   (prepend-column
                                    (vector-add 'left-tail 'right-tail)
                                    (matrix-addition
                                     empty-columns empty-columns))
                                   (matrix-addition
                                    (prepend-column
                                     'left-tail empty-columns)
                                    (prepend-column
                                     'right-tail empty-columns)))
                                  (app
                                   (function/const*
                                    'vector/equivalent-reflexive [])
                                   sum-singleton)
                                  output-tail-equivalent))))
                             (function/lam
                              [['right-column vector-type]
                               ['right-columns matrix-type]
                               ['ignored
                                (app right-columns-motive
                                     'right-columns)]]
                              (function/lam
                               [['candidate-columns-shape
                                 (matrix-same-shape
                                  empty-columns
                                  (cons-matrix
                                   'right-column 'right-columns))]]
                               (absurd
                                (prepend-additive-result
                                 current-left-values
                                 current-right-values
                                 empty-columns
                                 (cons-matrix
                                  'right-column 'right-columns))
                                'candidate-columns-shape)))
                             'candidate-right-columns)))
                         left-columns-step
                         (function/lam
                          [['left-column vector-type]
                           ['left-columns matrix-type]
                           ['ignored-left
                            (app left-columns-motive 'left-columns)]]
                          (let [current-left-columns
                                (cons-matrix
                                 'left-column 'left-columns)
                                right-columns-motive
                                (function/lam
                                 [['candidate-right-columns matrix-type]]
                                 (function/forall
                                  [['candidate-columns-shape
                                    (matrix-same-shape
                                     current-left-columns
                                     'candidate-right-columns)]]
                                  (prepend-additive-result
                                   current-left-values
                                   current-right-values
                                   current-left-columns
                                   'candidate-right-columns)))]
                            (function/lam
                             [['candidate-right-columns matrix-type]]
                             (matrix-rec
                              right-columns-motive
                              (function/lam
                               [['candidate-columns-shape
                                 (matrix-same-shape
                                  current-left-columns (nil-matrix))]]
                               (absurd
                                (prepend-additive-result
                                 current-left-values
                                 current-right-values
                                 current-left-columns (nil-matrix))
                                'candidate-columns-shape))
                              (function/lam
                               [['right-column vector-type]
                                ['right-columns matrix-type]
                                ['ignored-right
                                 (app right-columns-motive
                                      'right-columns)]]
                               (function/lam
                                [['candidate-columns-shape
                                  (matrix-same-shape
                                   current-left-columns
                                   (cons-matrix
                                    'right-column 'right-columns))]]
                                (let [columns-head-shape
                                      (vector-same-shape
                                       'left-column 'right-column)
                                      columns-tail-shape
                                      (matrix-same-shape
                                       'left-columns 'right-columns)
                                      tail-both
                                      (app 'tail-result
                                           'right-tail
                                           'left-columns 'right-columns
                                           tail-values-shape
                                           (proposition-right
                                            columns-head-shape
                                            columns-tail-shape
                                            'candidate-columns-shape))
                                      output-left-row
                                      (cons-vector
                                       'left-head 'left-column)
                                      output-right-row
                                      (cons-vector
                                       'right-head 'right-column)
                                      output-sum-row
                                      (cons-vector
                                       (signed-add
                                        'left-head 'right-head)
                                       (vector-add
                                        'left-column 'right-column))
                                      output-head-shape
                                      (conjoin
                                       values-head-shape
                                       columns-head-shape
                                       (app
                                        (function/const*
                                         'signed/equivalent-reflexive [])
                                        signed-zero)
                                       (proposition-left
                                        columns-head-shape
                                        columns-tail-shape
                                        'candidate-columns-shape))
                                      output-tail-shape
                                      (proposition-left
                                       (matrix-same-shape
                                        (prepend-column
                                         'left-tail 'left-columns)
                                        (prepend-column
                                         'right-tail 'right-columns))
                                       (matrix-equivalent
                                        (prepend-column
                                         (vector-add
                                          'left-tail 'right-tail)
                                         (matrix-addition
                                          'left-columns 'right-columns))
                                        (matrix-addition
                                         (prepend-column
                                          'left-tail 'left-columns)
                                         (prepend-column
                                          'right-tail 'right-columns)))
                                       tail-both)
                                      output-tail-equivalent
                                      (proposition-right
                                       (matrix-same-shape
                                        (prepend-column
                                         'left-tail 'left-columns)
                                        (prepend-column
                                         'right-tail 'right-columns))
                                       (matrix-equivalent
                                        (prepend-column
                                         (vector-add
                                          'left-tail 'right-tail)
                                         (matrix-addition
                                          'left-columns 'right-columns))
                                        (matrix-addition
                                         (prepend-column
                                          'left-tail 'left-columns)
                                         (prepend-column
                                          'right-tail 'right-columns)))
                                       tail-both)]
                                  (conjoin
                                   (matrix-same-shape
                                    (prepend-column
                                     current-left-values
                                     current-left-columns)
                                    (prepend-column
                                     current-right-values
                                     (cons-matrix
                                      'right-column 'right-columns)))
                                   (matrix-equivalent
                                    (prepend-column
                                     (vector-add
                                      current-left-values
                                      current-right-values)
                                     (matrix-addition
                                      current-left-columns
                                      (cons-matrix
                                       'right-column 'right-columns)))
                                    (matrix-addition
                                     (prepend-column
                                      current-left-values
                                      current-left-columns)
                                     (prepend-column
                                      current-right-values
                                      (cons-matrix
                                       'right-column 'right-columns))))
                                   (conjoin
                                    (vector-same-shape
                                     output-left-row output-right-row)
                                    (matrix-same-shape
                                     (prepend-column
                                      'left-tail 'left-columns)
                                     (prepend-column
                                      'right-tail 'right-columns))
                                    output-head-shape output-tail-shape)
                                   (conjoin
                                    (vector-equivalent
                                     output-sum-row output-sum-row)
                                    (matrix-equivalent
                                     (prepend-column
                                      (vector-add
                                       'left-tail 'right-tail)
                                      (matrix-addition
                                       'left-columns 'right-columns))
                                     (matrix-addition
                                      (prepend-column
                                       'left-tail 'left-columns)
                                      (prepend-column
                                       'right-tail 'right-columns)))
                                    (app
                                     (function/const*
                                      'vector/equivalent-reflexive [])
                                     output-sum-row)
                                    output-tail-equivalent)))))
                              'candidate-right-columns))))]
                     (app
                      (matrix-rec
                       left-columns-motive
                       left-columns-base
                       left-columns-step
                       'current-left-columns)
                      'current-right-columns
                      'current-columns-shape)))))
               'current-right-values))))]
      (app (vector-rec values-motive values-base values-step 'left-values)
           'right-values 'left-columns 'right-columns
           'values-shape 'columns-shape)))})

(def prepend-column-preserves-same-shape-spec
  {:name 'matrix/prepend-column-preserves-same-shape :universes []
   :type
   (function/forall
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (matrix-same-shape
     (prepend-column 'left-values 'left-columns)
     (prepend-column 'right-values 'right-columns)))
   :value
   (function/lam
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (proposition-left
     (matrix-same-shape
      (prepend-column 'left-values 'left-columns)
      (prepend-column 'right-values 'right-columns))
     (matrix-equivalent
      (prepend-column
       (vector-add 'left-values 'right-values)
       (matrix-addition 'left-columns 'right-columns))
      (matrix-addition
       (prepend-column 'left-values 'left-columns)
       (prepend-column 'right-values 'right-columns)))
     (app
      (function/const* 'matrix/prepend-column-additive-with-shape [])
      'left-values 'right-values 'left-columns 'right-columns
      'values-shape 'columns-shape)))})

(def prepend-column-additive-spec
  {:name 'matrix/prepend-column-additive :universes []
   :type
   (function/forall
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (matrix-equivalent
     (prepend-column
      (vector-add 'left-values 'right-values)
      (matrix-addition 'left-columns 'right-columns))
     (matrix-addition
      (prepend-column 'left-values 'left-columns)
      (prepend-column 'right-values 'right-columns))))
   :value
   (function/lam
    [['left-values vector-type] ['right-values vector-type]
     ['left-columns matrix-type] ['right-columns matrix-type]
     ['values-shape
      (vector-same-shape 'left-values 'right-values)]
     ['columns-shape
      (matrix-same-shape 'left-columns 'right-columns)]]
    (proposition-right
     (matrix-same-shape
      (prepend-column 'left-values 'left-columns)
      (prepend-column 'right-values 'right-columns))
     (matrix-equivalent
      (prepend-column
       (vector-add 'left-values 'right-values)
       (matrix-addition 'left-columns 'right-columns))
      (matrix-addition
       (prepend-column 'left-values 'left-columns)
       (prepend-column 'right-values 'right-columns)))
     (app
      (function/const* 'matrix/prepend-column-additive-with-shape [])
      'left-values 'right-values 'left-columns 'right-columns
      'values-shape 'columns-shape)))})

(def definition-specs [])
(def theorem-specs
  [prepend-column-additive-with-shape-spec
   prepend-column-preserves-same-shape-spec
   prepend-column-additive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.add-shape])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-prepend-add theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.prepend-add))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
