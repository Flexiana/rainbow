(ns rainbow.math.linear.matrix.transpose-involution
  "Algebraic foundations for nondegenerate transpose involution.

  A row-list matrix cannot retain the number of rows of a nonempty zero-width
  matrix: matrix/transpose of rows of empty vectors is empty.  Accordingly the
  eventual involution theorem must require positive width.  The first two
  native lemmas prove the core valid algebra: transpose undoes insertion of a
  nonempty vector into empty columns, and into nonempty columns whose remaining
  count matches the remaining vector width.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.transpose-shape :as transpose-shape]
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
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- matrix-transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- absurd [target impossible]
  (app impossible target))

(def transpose-prepend-column-empty-spec
  {:name 'matrix/transpose-prepend-column-empty :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]]
    (matrix-equivalent
     (matrix-transpose
      (prepend-column
       (cons-vector 'head 'tail) (nil-matrix)))
     (cons-matrix
      (cons-vector 'head 'tail) (nil-matrix))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]]
    (let [tail-motive
          (function/lam
           [['current-tail vector-type]]
           (function/forall
            [['current-head signed]]
            (matrix-equivalent
             (matrix-transpose
              (prepend-column
               (cons-vector 'current-head 'current-tail)
               (nil-matrix)))
             (cons-matrix
              (cons-vector 'current-head 'current-tail)
              (nil-matrix)))))
          tail-base
          (function/lam
           [['current-head signed]]
           (app (function/const* 'matrix/equivalent-reflexive [])
                (cons-matrix
                 (cons-vector 'current-head (nil-vector))
                 (nil-matrix))))
          tail-step
          (function/lam
           [['next signed] ['remaining vector-type]
            ['remaining-undoes (app tail-motive 'remaining)]]
           (function/lam
            [['current-head signed]]
            (app
             (function/const*
              'matrix/prepend-column-respects-matrix-equivalence [])
             (cons-vector 'current-head (nil-vector))
             (matrix-transpose
              (prepend-column
               (cons-vector 'next 'remaining) (nil-matrix)))
             (cons-matrix
              (cons-vector 'next 'remaining) (nil-matrix))
             (app 'remaining-undoes 'next))))]
      (app (vector-rec tail-motive tail-base tail-step 'tail) 'head)))})

(def transpose-prepend-column-cons-spec
  {:name 'matrix/transpose-prepend-column-cons :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]
     ['column vector-type] ['columns matrix-type]
     ['width (same-shape 'tail (column-shape 'columns))]]
    (matrix-equivalent
     (matrix-transpose
      (prepend-column
       (cons-vector 'head 'tail)
       (cons-matrix 'column 'columns)))
     (cons-matrix
      (cons-vector 'head 'tail)
      (matrix-transpose
       (cons-matrix 'column 'columns)))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]
     ['column vector-type] ['columns matrix-type]
     ['width (same-shape 'tail (column-shape 'columns))]]
    (let [tail-motive
          (function/lam
           [['current-tail vector-type]]
           (function/forall
            [['current-head signed]
             ['current-column vector-type]
             ['current-columns matrix-type]
             ['current-width
              (same-shape
               'current-tail (column-shape 'current-columns))]]
            (matrix-equivalent
             (matrix-transpose
              (prepend-column
               (cons-vector 'current-head 'current-tail)
               (cons-matrix 'current-column 'current-columns)))
             (cons-matrix
              (cons-vector 'current-head 'current-tail)
              (matrix-transpose
               (cons-matrix 'current-column 'current-columns))))))
          tail-base
          (let [empty (nil-vector)
                columns-motive
                (function/lam
                 [['current-columns matrix-type]]
                 (function/forall
                  [['current-head signed]
                   ['current-column vector-type]
                   ['current-width
                    (same-shape
                     empty (column-shape 'current-columns))]]
                  (matrix-equivalent
                   (matrix-transpose
                    (prepend-column
                     (cons-vector 'current-head empty)
                     (cons-matrix
                      'current-column 'current-columns)))
                   (cons-matrix
                    (cons-vector 'current-head empty)
                    (matrix-transpose
                     (cons-matrix
                      'current-column 'current-columns))))))]
            (function/lam
             [['current-head signed]
              ['current-column vector-type]
              ['current-columns matrix-type]
              ['current-width
               (same-shape empty (column-shape 'current-columns))]]
             (app
              (matrix-rec
               columns-motive
               (function/lam
                [['base-head signed] ['base-column vector-type]
                 ['base-width
                  (same-shape
                   empty (column-shape (nil-matrix)))]]
                (app (function/const* 'matrix/equivalent-reflexive [])
                     (cons-matrix
                      (cons-vector 'base-head empty)
                      (matrix-transpose
                       (cons-matrix
                        'base-column (nil-matrix))))))
               (function/lam
                [['extra-column vector-type]
                 ['remaining-columns matrix-type]
                 ['ignored (app columns-motive 'remaining-columns)]]
                (function/lam
                 [['base-head signed] ['base-column vector-type]
                  ['base-width
                   (same-shape
                    empty
                    (column-shape
                     (cons-matrix
                      'extra-column 'remaining-columns)))]]
                 (absurd
                  (matrix-equivalent
                   (matrix-transpose
                    (prepend-column
                     (cons-vector 'base-head empty)
                     (cons-matrix
                      'base-column
                      (cons-matrix
                       'extra-column 'remaining-columns))))
                   (cons-matrix
                    (cons-vector 'base-head empty)
                    (matrix-transpose
                     (cons-matrix
                      'base-column
                      (cons-matrix
                       'extra-column 'remaining-columns)))))
                  'base-width)))
               'current-columns)
              'current-head 'current-column 'current-width)))
          tail-step
          (function/lam
           [['next signed] ['remaining vector-type]
            ['remaining-undoes (app tail-motive 'remaining)]]
           (function/lam
            [['current-head signed]
             ['current-column vector-type]
             ['current-columns matrix-type]
             ['current-width
              (same-shape
               (cons-vector 'next 'remaining)
               (column-shape 'current-columns))]]
            (let [columns-motive
                  (function/lam
                   [['candidate-columns matrix-type]]
                   (function/forall
                    [['candidate-width
                      (same-shape
                       (cons-vector 'next 'remaining)
                       (column-shape 'candidate-columns))]]
                    (matrix-equivalent
                     (matrix-transpose
                      (prepend-column
                       (cons-vector
                        'current-head (cons-vector 'next 'remaining))
                       (cons-matrix
                        'current-column 'candidate-columns)))
                     (cons-matrix
                      (cons-vector
                       'current-head (cons-vector 'next 'remaining))
                      (matrix-transpose
                       (cons-matrix
                        'current-column 'candidate-columns))))))]
              (app
               (matrix-rec
                columns-motive
                (function/lam
                 [['candidate-width
                   (same-shape
                    (cons-vector 'next 'remaining)
                    (column-shape (nil-matrix)))]]
                 (absurd
                  (matrix-equivalent
                   (matrix-transpose
                    (prepend-column
                     (cons-vector
                      'current-head (cons-vector 'next 'remaining))
                     (cons-matrix
                      'current-column (nil-matrix))))
                   (cons-matrix
                    (cons-vector
                     'current-head (cons-vector 'next 'remaining))
                    (matrix-transpose
                     (cons-matrix
                      'current-column (nil-matrix)))))
                  'candidate-width))
                (function/lam
                 [['next-column vector-type]
                  ['remaining-columns matrix-type]
                  ['ignored (app columns-motive 'remaining-columns)]]
                 (function/lam
                  [['candidate-width
                    (same-shape
                     (cons-vector 'next 'remaining)
                     (column-shape
                      (cons-matrix
                       'next-column 'remaining-columns)))]]
                  (let [remaining-width
                        (proposition-right
                         (signed-equivalent
                          (function/const* 'signed/zero [])
                          (function/const* 'signed/zero []))
                         (same-shape
                          'remaining
                          (column-shape 'remaining-columns))
                         'candidate-width)
                        recursive-undoes
                        (app 'remaining-undoes
                             'next 'next-column 'remaining-columns
                             remaining-width)]
                    (app
                     (function/const*
                      'matrix/prepend-column-respects-matrix-equivalence [])
                     (cons-vector 'current-head 'current-column)
                     (matrix-transpose
                      (prepend-column
                       (cons-vector 'next 'remaining)
                       (cons-matrix
                        'next-column 'remaining-columns)))
                     (cons-matrix
                      (cons-vector 'next 'remaining)
                      (matrix-transpose
                       (cons-matrix
                        'next-column 'remaining-columns)))
                     recursive-undoes))))
                'current-columns)
               'current-width))))]
      (app (vector-rec tail-motive tail-base tail-step 'tail)
           'head 'column 'columns 'width)))})

(def definition-specs [])
(def theorem-specs
  [transpose-prepend-column-empty-spec
   transpose-prepend-column-cons-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose-shape])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-transpose-involution theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.transpose-involution))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
