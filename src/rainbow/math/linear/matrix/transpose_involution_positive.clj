(ns rainbow.math.linear.matrix.transpose-involution-positive
  "Transpose involution for rectangular matrices of positive width.

  Positive width is carried constructively by exposing the first row as
  `head :: tail`; no separate Boolean or existential certificate is needed.
  A nested-insertion lemma shows how transpose recovers the leading row.  Tail
  induction then proves double transpose matrix-equivalent to the input for
  every rectangular matrix with a nonempty first row.  This is the strongest
  valid theorem for the row-list representation: nonempty zero-width matrices
  lose their row count under transpose.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.transpose-involution :as involution]
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
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
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
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def transpose-prepend-column-after-prepend-spec
  {:name 'matrix/transpose-prepend-column-after-prepend :universes []
   :type
   (function/forall
    [['head signed] ['tail vector-type]
     ['next-head signed] ['next-tail vector-type]
     ['columns matrix-type]
     ['row-tails-shape (same-shape 'tail 'next-tail)]]
    (matrix-equivalent
     (matrix-transpose
      (prepend-column
       (cons-vector 'head 'tail)
       (prepend-column
        (cons-vector 'next-head 'next-tail) 'columns)))
     (cons-matrix
      (cons-vector 'head 'tail)
      (matrix-transpose
       (prepend-column
        (cons-vector 'next-head 'next-tail) 'columns)))))
   :value
   (function/lam
    [['head signed] ['tail vector-type]
     ['next-head signed] ['next-tail vector-type]
     ['columns matrix-type]
     ['row-tails-shape (same-shape 'tail 'next-tail)]]
    (let [columns-motive
          (function/lam
           [['current-columns matrix-type]]
           (function/forall
            [['current-head signed] ['current-tail vector-type]
             ['current-next-head signed]
             ['current-next-tail vector-type]
             ['current-row-tails-shape
              (same-shape 'current-tail 'current-next-tail)]]
            (matrix-equivalent
             (matrix-transpose
              (prepend-column
               (cons-vector 'current-head 'current-tail)
               (prepend-column
                (cons-vector
                 'current-next-head 'current-next-tail)
                'current-columns)))
             (cons-matrix
              (cons-vector 'current-head 'current-tail)
              (matrix-transpose
               (prepend-column
                (cons-vector
                 'current-next-head 'current-next-tail)
                'current-columns))))))
          columns-base
          (function/lam
           [['current-head signed] ['current-tail vector-type]
            ['current-next-head signed]
            ['current-next-tail vector-type]
            ['current-row-tails-shape
             (same-shape 'current-tail 'current-next-tail)]]
           (let [next-output-shape
                 (app
                  (function/const*
                   'matrix/prepend-column-output-shape [])
                  'current-next-tail (nil-matrix))
                 next-tail-columns-shape
                 (app (function/const* 'vector/same-shape-symmetric [])
                      (column-shape
                       (prepend-column
                        'current-next-tail (nil-matrix)))
                      'current-next-tail next-output-shape)
                 current-width
                 (app (function/const* 'vector/same-shape-transitive [])
                      'current-tail 'current-next-tail
                      (column-shape
                       (prepend-column
                        'current-next-tail (nil-matrix)))
                      'current-row-tails-shape
                      next-tail-columns-shape)]
             (app
              (function/const* 'matrix/transpose-prepend-column-cons [])
              'current-head 'current-tail
              (cons-vector 'current-next-head (nil-vector))
              (prepend-column 'current-next-tail (nil-matrix))
              current-width)))
          columns-step
          (function/lam
           [['column vector-type] ['remaining-columns matrix-type]
            ['ignored (app columns-motive 'remaining-columns)]]
           (function/lam
            [['current-head signed] ['current-tail vector-type]
             ['current-next-head signed]
             ['current-next-tail vector-type]
             ['current-row-tails-shape
              (same-shape 'current-tail 'current-next-tail)]]
            (let [next-output-shape
                  (app
                   (function/const*
                    'matrix/prepend-column-output-shape [])
                   'current-next-tail 'remaining-columns)
                  next-tail-columns-shape
                  (app (function/const* 'vector/same-shape-symmetric [])
                       (column-shape
                        (prepend-column
                         'current-next-tail 'remaining-columns))
                       'current-next-tail next-output-shape)
                  current-width
                  (app (function/const* 'vector/same-shape-transitive [])
                       'current-tail 'current-next-tail
                       (column-shape
                        (prepend-column
                         'current-next-tail 'remaining-columns))
                       'current-row-tails-shape
                       next-tail-columns-shape)]
              (app
               (function/const* 'matrix/transpose-prepend-column-cons [])
               'current-head 'current-tail
               (cons-vector 'current-next-head 'column)
               (prepend-column 'current-next-tail 'remaining-columns)
               current-width))))]
      (app (matrix-rec columns-motive columns-base columns-step 'columns)
           'head 'tail 'next-head 'next-tail 'row-tails-shape)))})

(def transpose-involutive-nonempty-width-spec
  {:name 'matrix/transpose-involutive-nonempty-width :universes []
   :type
   (function/forall
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (matrix-equivalent
     (matrix-transpose
      (matrix-transpose
       (cons-matrix (cons-vector 'head 'row-tail) 'tail)))
     (cons-matrix (cons-vector 'head 'row-tail) 'tail)))
   :value
   (function/lam
    [['head signed] ['row-tail vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular
       (cons-matrix (cons-vector 'head 'row-tail) 'tail))]]
    (let [tail-motive
          (function/lam
           [['current-tail matrix-type]]
           (function/forall
            [['current-head signed] ['current-row-tail vector-type]
             ['current-rectangular
              (rectangular
               (cons-matrix
                (cons-vector 'current-head 'current-row-tail)
                'current-tail))]]
            (matrix-equivalent
             (matrix-transpose
              (matrix-transpose
               (cons-matrix
                (cons-vector 'current-head 'current-row-tail)
                'current-tail)))
             (cons-matrix
              (cons-vector 'current-head 'current-row-tail)
              'current-tail))))
          tail-base
          (function/lam
           [['current-head signed] ['current-row-tail vector-type]
            ['current-rectangular
             (rectangular
              (cons-matrix
               (cons-vector 'current-head 'current-row-tail)
               (nil-matrix)))]]
           (app
            (function/const* 'matrix/transpose-prepend-column-empty [])
            'current-head 'current-row-tail))
          tail-step
          (function/lam
           [['second vector-type] ['rest matrix-type]
            ['rest-involutive (app tail-motive 'rest)]]
           (let [current-tail (cons-matrix 'second 'rest)
                 second-motive
                 (function/lam
                  [['current-second vector-type]]
                  (function/forall
                   [['current-head signed]
                    ['current-row-tail vector-type]
                    ['current-rectangular
                     (rectangular
                      (cons-matrix
                       (cons-vector
                        'current-head 'current-row-tail)
                       (cons-matrix 'current-second 'rest)))]]
                   (matrix-equivalent
                    (matrix-transpose
                     (matrix-transpose
                      (cons-matrix
                       (cons-vector
                        'current-head 'current-row-tail)
                       (cons-matrix 'current-second 'rest))))
                    (cons-matrix
                     (cons-vector 'current-head 'current-row-tail)
                     (cons-matrix 'current-second 'rest)))))]
             (function/lam
              [['current-head signed] ['current-row-tail vector-type]
               ['current-rectangular
                (rectangular
                 (cons-matrix
                  (cons-vector 'current-head 'current-row-tail)
                  current-tail))]]
              (app
               (vector-rec
                second-motive
                (function/lam
                 [['empty-current-head signed]
                  ['empty-current-row-tail vector-type]
                  ['empty-current-rectangular
                   (rectangular
                    (cons-matrix
                     (cons-vector
                      'empty-current-head 'empty-current-row-tail)
                     (cons-matrix (nil-vector) 'rest)))]]
                 (let [impossible-shape
                       (app
                        (function/const*
                         'matrix/compatible-head-shape [])
                        (nil-vector) 'rest
                        (cons-vector
                         'empty-current-head 'empty-current-row-tail)
                        'empty-current-rectangular)]
                   (absurd
                    (matrix-equivalent
                     (matrix-transpose
                      (matrix-transpose
                       (cons-matrix
                        (cons-vector
                         'empty-current-head 'empty-current-row-tail)
                        (cons-matrix (nil-vector) 'rest))))
                     (cons-matrix
                      (cons-vector
                       'empty-current-head 'empty-current-row-tail)
                      (cons-matrix (nil-vector) 'rest)))
                    impossible-shape)))
                (function/lam
                 [['second-head signed] ['second-tail vector-type]
                  ['ignored (app second-motive 'second-tail)]]
                 (function/lam
                  [['nonempty-current-head signed]
                   ['nonempty-current-row-tail vector-type]
                   ['nonempty-current-rectangular
                    (rectangular
                     (cons-matrix
                      (cons-vector
                       'nonempty-current-head
                       'nonempty-current-row-tail)
                      (cons-matrix
                       (cons-vector 'second-head 'second-tail)
                       'rest)))]]
                  (let [current-row
                        (cons-vector
                         'nonempty-current-head
                         'nonempty-current-row-tail)
                        nonempty-current-tail
                        (cons-matrix
                         (cons-vector 'second-head 'second-tail)
                         'rest)
                        second-row-shape
                        (app
                         (function/const*
                          'matrix/compatible-head-shape [])
                         (cons-vector 'second-head 'second-tail)
                         'rest current-row
                         'nonempty-current-rectangular)
                        second-tail-row-tail-shape
                        (proposition-right
                         (signed-equivalent signed-zero signed-zero)
                         (same-shape
                          'second-tail 'nonempty-current-row-tail)
                         second-row-shape)
                        row-tail-second-tail-shape
                        (app
                         (function/const*
                          'vector/same-shape-symmetric [])
                         'second-tail 'nonempty-current-row-tail
                         second-tail-row-tail-shape)
                        leading-row-recovered
                        (app
                         (function/const*
                          'matrix/transpose-prepend-column-after-prepend [])
                         'nonempty-current-head
                         'nonempty-current-row-tail
                         'second-head 'second-tail
                         (matrix-transpose 'rest)
                         row-tail-second-tail-shape)
                        tail-rectangular
                        (app
                         (function/const* 'matrix/rectangular-tail [])
                         current-row nonempty-current-tail
                         'nonempty-current-rectangular)
                        tail-involutive
                        (app 'rest-involutive
                             'second-head 'second-tail tail-rectangular)
                        tail-lifted
                        (conjoin
                         (vector-equivalent current-row current-row)
                         (matrix-equivalent
                          (matrix-transpose
                           (matrix-transpose nonempty-current-tail))
                          nonempty-current-tail)
                         (app
                          (function/const*
                           'vector/equivalent-reflexive [])
                          current-row)
                         tail-involutive)]
                    (app
                     (function/const* 'matrix/equivalent-transitive [])
                     (matrix-transpose
                      (matrix-transpose
                       (cons-matrix current-row nonempty-current-tail)))
                     (cons-matrix
                      current-row
                      (matrix-transpose
                       (matrix-transpose nonempty-current-tail)))
                     (cons-matrix current-row nonempty-current-tail)
                     leading-row-recovered tail-lifted))))
                'second)
               'current-head 'current-row-tail
               'current-rectangular))))]
      (app (matrix-rec tail-motive tail-base tail-step 'tail)
           'head 'row-tail 'rows-rectangular)))})

(def definition-specs [])
(def theorem-specs
  [transpose-prepend-column-after-prepend-spec
   transpose-involutive-nonempty-width-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      involution/extend-environment
      (support/extend-with
       :finite-matrix-transpose-involution-positive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
