(ns rainbow.math.linear.matrix.action-associative
  "Finite matrix action is adjoint to native transpose.

      dot (matrix/vector-multiply (transpose rows) coefficients) values
        ~ dot coefficients (matrix/vector-multiply rows values)

  Coefficients must have one component per row and every row must match the
  value vector.  Empty, singleton, and multirow cases are separate opaque
  boundaries so the small kernel need not normalize transpose, column
  insertion, dot, and nested List recursors simultaneously.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.action-prepend :as prepend]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
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
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- prepend-column [values columns]
  (app (function/const* 'matrix/prepend-column []) values columns))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- same-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- action-goal [rows coefficients values]
  (signed-equivalent
   (dot (vector-multiply (transpose rows) coefficients) values)
   (dot coefficients (vector-multiply rows values))))

(defn- action-law [rows]
  (function/forall
   [['coefficients vector-type] ['values vector-type]
    ['coefficient-shape
     (same-shape 'coefficients (column-shape rows))]
    ['rows-compatible (compatible rows 'values)]]
   (action-goal rows 'coefficients 'values)))

(def dot-cons-singleton-spec
  {:name 'vector/dot-cons-singleton :universes []
   :type
   (function/forall
    [['coefficient signed] ['coefficient-tail vector-type]
     ['value signed]]
    (signed-equivalent
     (dot
      (cons-vector 'coefficient 'coefficient-tail)
      (cons-vector 'value (nil-vector)))
     (signed-multiply 'coefficient 'value)))
   :value
   (function/lam
    [['coefficient signed] ['coefficient-tail vector-type]
     ['value signed]]
    (let [product (signed-multiply 'coefficient 'value)
          tail-dot (dot 'coefficient-tail (nil-vector))
          start (signed-add product tail-dot)
          middle (signed-add product signed-zero)]
      (transitive
       start middle product
       (app (function/const* 'signed/add-respects-equivalence [])
            product product tail-dot signed-zero
            (app (function/const* 'signed/equivalent-reflexive []) product)
            (app (function/const* 'vector/dot-zero-like-right [])
                 'coefficient-tail (nil-vector)))
       (app (function/const* 'signed/add-zero-right []) product))))})

(def action-associative-empty-spec
  {:name 'matrix/vector-action-associative-empty :universes []
   :type
   (function/forall
    [['coefficients vector-type] ['values vector-type]]
    (action-goal (nil-matrix) 'coefficients 'values))
   :value
   (function/lam
    [['coefficients vector-type] ['values vector-type]]
    (symmetric
     (dot 'coefficients (nil-vector)) signed-zero
     (app (function/const* 'vector/dot-zero-like-right [])
          'coefficients (nil-vector))))})

(def action-associative-single-spec
  {:name 'matrix/vector-action-associative-single :universes []
   :type
   (function/forall
    [['row vector-type] ['coefficient signed]
     ['coefficient-tail vector-type] ['values vector-type]]
    (action-goal
     (cons-matrix 'row (nil-matrix))
     (cons-vector 'coefficient 'coefficient-tail)
     'values))
   :value
   (function/lam
    [['row vector-type] ['coefficient signed]
     ['coefficient-tail vector-type] ['values vector-type]]
    (let [rows (cons-matrix 'row (nil-matrix))
          coefficients (cons-vector 'coefficient 'coefficient-tail)
          inserted-action
          (vector-multiply
           (prepend-column 'row (nil-matrix)) coefficients)
          scaled (signed-scale 'coefficient 'row)
          product (signed-multiply 'coefficient (dot 'row 'values))
          start (dot (vector-multiply (transpose rows) coefficients) 'values)
          scaled-dot (dot scaled 'values)
          finish (dot coefficients (vector-multiply rows 'values))]
      (transitive
       start product finish
       (transitive
        start scaled-dot product
        (app (function/const* 'vector/dot-left-respects-equivalence [])
             inserted-action scaled 'values
             (app
              (function/const*
               'matrix/vector-multiply-prepend-column-empty [])
              'coefficient 'row 'coefficient-tail))
        (app (function/const* 'vector/dot-signed-scale-left [])
             'coefficient 'row 'values))
       (symmetric
        finish product
        (app (function/const* 'vector/dot-cons-singleton [])
             'coefficient 'coefficient-tail (dot 'row 'values))))))})

(def action-associative-cons-cons-spec
  {:name 'matrix/vector-action-associative-cons-cons :universes []
   :type
   (function/forall
    [['row vector-type] ['second vector-type] ['rest matrix-type]
     ['coefficient signed] ['coefficient-tail vector-type]
     ['values vector-type]
     ['rows-compatible
      (compatible
       (cons-matrix 'row (cons-matrix 'second 'rest)) 'values)]
     ['tail-associative
      (action-goal
       (cons-matrix 'second 'rest) 'coefficient-tail 'values)]]
    (action-goal
     (cons-matrix 'row (cons-matrix 'second 'rest))
     (cons-vector 'coefficient 'coefficient-tail)
     'values))
   :value
   (function/lam
    [['row vector-type] ['second vector-type] ['rest matrix-type]
     ['coefficient signed] ['coefficient-tail vector-type]
     ['values vector-type]
     ['rows-compatible
      (compatible
       (cons-matrix 'row (cons-matrix 'second 'rest)) 'values)]
     ['tail-associative
      (action-goal
       (cons-matrix 'second 'rest) 'coefficient-tail 'values)]]
    (let [tail (cons-matrix 'second 'rest)
          rows (cons-matrix 'row tail)
          coefficients (cons-vector 'coefficient 'coefficient-tail)
          tail-transpose (transpose tail)
          inserted-action
          (vector-multiply
           (prepend-column 'row tail-transpose) coefficients)
          scaled-row (signed-scale 'coefficient 'row)
          tail-action
          (vector-multiply tail-transpose 'coefficient-tail)
          combined-action (vector-add scaled-row tail-action)
          start
          (dot (vector-multiply (transpose rows) coefficients) 'values)
          decomposed (dot combined-action 'values)
          split
          (signed-add
           (dot scaled-row 'values)
           (dot tail-action 'values))
          finish (dot coefficients (vector-multiply rows 'values))
          rows-rectangular
          (app (function/const* 'matrix/compatible-implies-rectangular [])
               rows 'values 'rows-compatible)
          second-row-shape
          (app (function/const* 'matrix/compatible-head-shape [])
               'second 'rest 'row rows-rectangular)
          row-second-shape
          (same-shape-symmetric 'second 'row second-row-shape)
          transpose-output-shape
          (app (function/const* 'matrix/prepend-column-output-shape [])
               'second (transpose 'rest))
          second-transpose-shape
          (same-shape-symmetric
           (column-shape tail-transpose) 'second
           transpose-output-shape)
          row-transpose-shape
          (same-shape-transitive
           'row 'second (column-shape tail-transpose)
           row-second-shape second-transpose-shape)
          scaled-row-shape
          (app (function/const* 'vector/signed-scale-preserves-shape [])
               'coefficient 'row)
          tail-action-shape
          (app (function/const* 'matrix/vector-multiply-column-shape [])
               tail-transpose 'coefficient-tail)
          transpose-tail-action-shape
          (same-shape-symmetric
           tail-action (column-shape tail-transpose) tail-action-shape)
          scaled-transpose-shape
          (same-shape-transitive
           scaled-row 'row (column-shape tail-transpose)
           scaled-row-shape row-transpose-shape)
          summands-shape
          (same-shape-transitive
           scaled-row (column-shape tail-transpose) tail-action
           scaled-transpose-shape transpose-tail-action-shape)]
      (transitive
       start split finish
       (transitive
        start decomposed split
        (app (function/const* 'vector/dot-left-respects-equivalence [])
             inserted-action combined-action 'values
             (app
              (function/const* 'matrix/vector-multiply-prepend-column [])
              'coefficient 'row tail-transpose 'coefficient-tail
              row-transpose-shape))
        (app (function/const* 'vector/dot-additive-left [])
             scaled-row tail-action 'values summands-shape))
       (app (function/const* 'signed/add-respects-equivalence [])
            (dot scaled-row 'values)
            (signed-multiply 'coefficient (dot 'row 'values))
            (dot tail-action 'values)
            (dot 'coefficient-tail (vector-multiply tail 'values))
            (app (function/const* 'vector/dot-signed-scale-left [])
                 'coefficient 'row 'values)
            'tail-associative))))})

(def action-associative-cons-spec
  {:name 'matrix/vector-action-associative-cons :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type]
     ['tail-law (action-law 'tail)]
     ['coefficients vector-type] ['values vector-type]
     ['coefficient-shape
      (same-shape
       'coefficients (column-shape (cons-matrix 'row 'tail)))]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (action-goal
     (cons-matrix 'row 'tail) 'coefficients 'values))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type]
     ['tail-law (action-law 'tail)]
     ['coefficients vector-type] ['values vector-type]
     ['coefficient-shape
      (same-shape
       'coefficients (column-shape (cons-matrix 'row 'tail)))]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (let [coefficient-motive
          (function/lam
           [['current-coefficients vector-type]]
           (function/forall
            [['current-shape
              (same-shape
               'current-coefficients
               (column-shape (cons-matrix 'row 'tail)))]
             ['current-compatible
              (compatible (cons-matrix 'row 'tail) 'values)]]
            (action-goal
             (cons-matrix 'row 'tail)
             'current-coefficients 'values)))
          coefficient-base
          (function/lam
           [['current-shape
             (same-shape
              (nil-vector)
              (column-shape (cons-matrix 'row 'tail)))]
            ['current-compatible
             (compatible (cons-matrix 'row 'tail) 'values)]]
           (absurd
            (action-goal
             (cons-matrix 'row 'tail) (nil-vector) 'values)
            'current-shape))
          coefficient-step
          (function/lam
           [['coefficient signed] ['coefficient-tail vector-type]
            ['ignored (app coefficient-motive 'coefficient-tail)]]
           (function/lam
            [['current-shape
              (same-shape
               (cons-vector 'coefficient 'coefficient-tail)
               (column-shape (cons-matrix 'row 'tail)))]
             ['current-compatible
              (compatible (cons-matrix 'row 'tail) 'values)]]
            (let [tail-shape
                  (proposition-right
                   (signed-equivalent signed-zero signed-zero)
                   (same-shape 'coefficient-tail (column-shape 'tail))
                   'current-shape)
                  tail-motive
                  (function/lam
                   [['current-tail matrix-type]]
                   (function/forall
                    [['current-tail-law (action-law 'current-tail)]
                     ['current-tail-shape
                      (same-shape
                       'coefficient-tail
                       (column-shape 'current-tail))]
                     ['current-rows-compatible
                      (compatible
                       (cons-matrix 'row 'current-tail) 'values)]]
                    (action-goal
                     (cons-matrix 'row 'current-tail)
                     (cons-vector 'coefficient 'coefficient-tail)
                     'values)))
                  tail-base
                  (function/lam
                   [['current-tail-law (action-law (nil-matrix))]
                    ['current-tail-shape
                     (same-shape
                      'coefficient-tail (column-shape (nil-matrix)))]
                    ['current-rows-compatible
                     (compatible
                      (cons-matrix 'row (nil-matrix)) 'values)]]
                   (app
                    (function/const*
                     'matrix/vector-action-associative-single [])
                    'row 'coefficient 'coefficient-tail 'values))
                  tail-step
                  (function/lam
                   [['second vector-type] ['rest matrix-type]
                    ['ignored-tail (app tail-motive 'rest)]]
                   (function/lam
                    [['current-tail-law
                      (action-law (cons-matrix 'second 'rest))]
                     ['current-tail-shape
                      (same-shape
                       'coefficient-tail
                       (column-shape (cons-matrix 'second 'rest)))]
                     ['current-rows-compatible
                      (compatible
                       (cons-matrix
                        'row (cons-matrix 'second 'rest)) 'values)]]
                    (let [tail-compatible
                          (app (function/const* 'matrix/compatible-tail [])
                               'row (cons-matrix 'second 'rest) 'values
                               'current-rows-compatible)
                          tail-associative
                          (app 'current-tail-law
                               'coefficient-tail 'values
                               'current-tail-shape tail-compatible)]
                      (app
                       (function/const*
                        'matrix/vector-action-associative-cons-cons [])
                       'row 'second 'rest
                       'coefficient 'coefficient-tail 'values
                       'current-rows-compatible tail-associative))))]
              (app
               (matrix-rec tail-motive tail-base tail-step 'tail)
               'tail-law tail-shape 'current-compatible))))]
      (app
       (vector-rec coefficient-motive
                   coefficient-base coefficient-step 'coefficients)
       'coefficient-shape 'rows-compatible)))})

(def vector-action-associative-spec
  {:name 'matrix/vector-action-associative :universes []
   :type
   (function/forall
    [['rows matrix-type] ['coefficients vector-type]
     ['values vector-type]
     ['coefficient-shape
      (same-shape 'coefficients (column-shape 'rows))]
     ['rows-compatible (compatible 'rows 'values)]]
    (action-goal 'rows 'coefficients 'values))
   :value
   (function/lam
    [['rows matrix-type] ['coefficients vector-type]
     ['values vector-type]
     ['coefficient-shape
      (same-shape 'coefficients (column-shape 'rows))]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [motive (function/lam [['current-rows matrix-type]]
                               (action-law 'current-rows))
          base
          (function/lam
           [['current-coefficients vector-type]
            ['current-values vector-type]
            ['current-shape
             (same-shape
              'current-coefficients (column-shape (nil-matrix)))]
            ['current-compatible
             (compatible (nil-matrix) 'current-values)]]
           (app
            (function/const* 'matrix/vector-action-associative-empty [])
            'current-coefficients 'current-values))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-law (app motive 'tail)]]
           (function/lam
            [['current-coefficients vector-type]
             ['current-values vector-type]
             ['current-shape
              (same-shape
               'current-coefficients
               (column-shape (cons-matrix 'row 'tail)))]
             ['current-compatible
              (compatible
               (cons-matrix 'row 'tail) 'current-values)]]
            (app
             (function/const* 'matrix/vector-action-associative-cons [])
             'row 'tail 'tail-law
             'current-coefficients 'current-values
             'current-shape 'current-compatible)))]
      (app
       (matrix-rec motive base step 'rows)
       'coefficients 'values
       'coefficient-shape 'rows-compatible)))})

(def definition-specs [])
(def theorem-specs
  [dot-cons-singleton-spec
   action-associative-empty-spec
   action-associative-single-spec
   action-associative-cons-cons-spec
   action-associative-cons-spec
   vector-action-associative-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.action-prepend])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'matrix/compatible-tail :finite-matrix-shape matrix-shape/compatible-tail-spec) (support/extend-with :finite-matrix-action-associative theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.action-associative))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
