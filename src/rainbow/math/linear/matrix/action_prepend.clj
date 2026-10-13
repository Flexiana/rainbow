(ns rainbow.math.linear.matrix.action-prepend
  "Action laws for inserting a leading column into a native finite matrix.

  Acting on a column inserted into no prior columns yields exactly the signed
  scaling of that column.  With existing columns, equal row/column count is the
  necessary premise for the usual decomposition into the scaled inserted
  column plus the old matrix action; without it native vector/add truncation
  makes the statement false.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.action-scale :as scale]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as signed-units]
            [rainbow.math.linear.vector.add-order :as add-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
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
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
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
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
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

(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))

(defn- prepend-action-goal [factor values columns weights]
  (vector-equivalent
   (vector-multiply
    (prepend-column values columns)
    (cons-vector factor weights))
   (vector-add
    (signed-scale factor values)
    (vector-multiply columns weights))))

(def multiply-to-scale-difference-spec
  {:name 'signed/multiply-to-scale-difference :universes []
   :type
   (function/forall
    [['value signed] ['factor signed]]
    (signed-equivalent
     (signed-multiply 'value 'factor)
     (scale-difference 'factor 'value)))
   :value
   (function/lam
    [['value signed] ['factor signed]]
    (let [start (signed-multiply 'value 'factor)
          middle (signed-multiply 'factor 'value)
          finish (scale-difference 'factor 'value)]
      (transitive
       start middle finish
       (app (function/const* 'signed/multiply-commutative [])
            'value 'factor)
       (symmetric
        finish middle
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor 'value)))))})

(def prepend-action-head-spec
  {:name 'signed/prepend-action-head :universes []
   :type
   (function/forall
    [['value signed] ['factor signed] ['tail-product signed]]
    (signed-equivalent
     (signed-add
      (signed-multiply 'value 'factor) 'tail-product)
     (signed-add
      (scale-difference 'factor 'value) 'tail-product)))
   :value
   (function/lam
    [['value signed] ['factor signed] ['tail-product signed]]
    (app (function/const* 'signed/add-respects-equivalence [])
         (signed-multiply 'value 'factor)
         (scale-difference 'factor 'value)
         'tail-product 'tail-product
         (app (function/const* 'signed/multiply-to-scale-difference [])
              'value 'factor)
         (app (function/const* 'signed/equivalent-reflexive [])
              'tail-product)))})

(def prepend-action-empty-head-spec
  {:name 'signed/prepend-action-empty-head :universes []
   :type
   (function/forall
    [['value signed] ['factor signed]]
    (signed-equivalent
     (signed-add (signed-multiply 'value 'factor) signed-zero)
     (scale-difference 'factor 'value)))
   :value
   (function/lam
    [['value signed] ['factor signed]]
    (let [start
          (signed-add (signed-multiply 'value 'factor) signed-zero)
          middle (signed-multiply 'value 'factor)
          finish (scale-difference 'factor 'value)]
      (transitive
       start middle finish
       (app (function/const* 'signed/add-zero-right [])
            (signed-multiply 'value 'factor))
       (app (function/const* 'signed/multiply-to-scale-difference [])
            'value 'factor))))})

(def vector-multiply-prepend-column-empty-spec
  {:name 'matrix/vector-multiply-prepend-column-empty :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (vector-equivalent
     (vector-multiply
      (prepend-column 'values (nil-matrix))
      (cons-vector 'factor 'weights))
     (signed-scale 'factor 'values)))
   :value
   (function/lam
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-multiply
             (prepend-column 'current (nil-matrix))
             (cons-vector 'factor 'weights))
            (signed-scale 'factor 'current)))
          step
          (function/lam
           [['value signed] ['tail vector-type]
            ['tail-action (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-add
              (signed-multiply 'value 'factor) signed-zero)
             (scale-difference 'factor 'value))
            (vector-equivalent
             (vector-multiply
              (prepend-column 'tail (nil-matrix))
              (cons-vector 'factor 'weights))
             (signed-scale 'factor 'tail))
            (app (function/const* 'signed/prepend-action-empty-head [])
                 'value 'factor)
            'tail-action))]
      (vector-rec motive trivial step 'values)))})

(def vector-multiply-prepend-column-spec
  {:name 'matrix/vector-multiply-prepend-column :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type] ['columns matrix-type]
     ['weights vector-type]
     ['shape (same-shape 'values (column-shape 'columns))]]
    (prepend-action-goal 'factor 'values 'columns 'weights))
   :value
   (function/lam
    [['factor signed] ['values vector-type] ['columns matrix-type]
     ['weights vector-type]
     ['shape (same-shape 'values (column-shape 'columns))]]
    (let [values-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-columns matrix-type]
             ['current-weights vector-type]
             ['current-shape
              (same-shape
               'current-values (column-shape 'current-columns))]]
            (prepend-action-goal
             'factor 'current-values 'current-columns 'current-weights)))
          values-base
          (let [empty (nil-vector)
                columns-motive
                (function/lam
                 [['current-columns matrix-type]]
                 (function/forall
                  [['current-weights vector-type]
                   ['current-shape
                    (same-shape empty (column-shape 'current-columns))]]
                  (prepend-action-goal
                   'factor empty 'current-columns 'current-weights)))]
            (function/lam
             [['current-columns matrix-type]]
             (matrix-rec
              columns-motive
              (function/lam
               [['current-weights vector-type]
                ['current-shape
                 (same-shape empty (column-shape (nil-matrix)))]]
               trivial)
              (function/lam
               [['column vector-type] ['remaining-columns matrix-type]
                ['ignored (app columns-motive 'remaining-columns)]]
               (function/lam
                [['current-weights vector-type]
                 ['current-shape
                  (same-shape
                   empty
                   (column-shape
                    (cons-matrix 'column 'remaining-columns)))]]
                (absurd
                 (prepend-action-goal
                  'factor empty
                  (cons-matrix 'column 'remaining-columns)
                  'current-weights)
                 'current-shape)))
              'current-columns)))
          values-step
          (function/lam
           [['value signed] ['tail vector-type]
            ['tail-action (app values-motive 'tail)]]
           (let [current-values (cons-vector 'value 'tail)
                 columns-motive
                 (function/lam
                  [['current-columns matrix-type]]
                  (function/forall
                   [['current-weights vector-type]
                    ['current-shape
                     (same-shape
                      current-values
                      (column-shape 'current-columns))]]
                   (prepend-action-goal
                    'factor current-values
                    'current-columns 'current-weights)))]
             (function/lam
              [['current-columns matrix-type]]
              (matrix-rec
               columns-motive
               (function/lam
                [['current-weights vector-type]
                 ['current-shape
                  (same-shape
                   current-values (column-shape (nil-matrix)))]]
                (absurd
                 (prepend-action-goal
                  'factor current-values (nil-matrix) 'current-weights)
                 'current-shape))
               (function/lam
                [['column vector-type] ['remaining-columns matrix-type]
                 ['ignored (app columns-motive 'remaining-columns)]]
                (function/lam
                 [['current-weights vector-type]
                  ['current-shape
                   (same-shape
                    current-values
                    (column-shape
                     (cons-matrix 'column 'remaining-columns)))]]
                 (let [head-shape
                       (signed-equivalent signed-zero signed-zero)
                       tail-shape
                       (same-shape 'tail
                                   (column-shape 'remaining-columns))
                       remaining-shape
                       (proposition-right
                        head-shape tail-shape 'current-shape)
                       tail-product (dot 'column 'current-weights)]
                   (conjoin
                    (signed-equivalent
                     (signed-add
                      (signed-multiply 'value 'factor) tail-product)
                     (signed-add
                      (scale-difference 'factor 'value) tail-product))
                    (prepend-action-goal
                     'factor 'tail 'remaining-columns 'current-weights)
                    (app (function/const* 'signed/prepend-action-head [])
                         'value 'factor tail-product)
                    (app 'tail-action
                         'remaining-columns 'current-weights
                         remaining-shape)))))
               'current-columns))))]
      (app
       (vector-rec values-motive values-base values-step 'values)
       'columns 'weights 'shape)))})

(def definition-specs [])
(def theorem-specs
  [multiply-to-scale-difference-spec
   prepend-action-head-spec
   prepend-action-empty-head-spec
   vector-multiply-prepend-column-empty-spec
   vector-multiply-prepend-column-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.action-scale])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/add-zero-right :signed-limit-uniqueness signed-units/signed-add-zero-right-spec) (extend-spec-if-missing 'vector/add-respects-equivalence :vector-add-order add-order/add-respects-equivalence-spec) (support/extend-with :finite-matrix-action-prepend theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.action-prepend))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
