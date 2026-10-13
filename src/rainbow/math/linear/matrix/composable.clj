(ns rainbow.math.linear.matrix.composable
  "Dimension certificates for native finite matrix composition.

  matrix/composable left right combines the exact inner-dimension condition
  (every left row has the shape of right's row-count vector) with rectangularity
  of right.  Compatibility itself forces left rectangularity, so projections
  recover both operand shape facts.  Column-shape respects matrix equivalence,
  and the full composability certificate transports across equivalent operands.
  This is the quotient-safe precondition for later associativity.  Native and
  axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.equivalence-shape :as equivalence-shape]
            [rainbow.math.linear.matrix.multiply-shape :as multiply-shape]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
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
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- composable [left right]
  (app (function/const* 'matrix/composable []) left right))
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

(def composable-spec
  {:name 'matrix/composable :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type 'Prop)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (conjunction
     (compatible 'left (column-shape 'right))
     (rectangular 'right)))})

(def compatible-implies-rectangular-spec
  {:name 'matrix/compatible-implies-rectangular :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (rectangular 'rows))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]
     ['rows-compatible (compatible 'rows 'values)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-values vector-type]
             ['current-compatible
              (compatible 'current-rows 'current-values)]]
            (rectangular 'current-rows)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['ignored (app motive 'tail)]]
           (function/lam
            [['current-values vector-type]
             ['current-compatible
              (compatible (cons-matrix 'row 'tail) 'current-values)]]
            (let [row-values-shape
                  (proposition-left
                   (same-shape 'row 'current-values)
                   (compatible 'tail 'current-values)
                   'current-compatible)
                  values-row-shape
                  (app (function/const* 'vector/same-shape-symmetric [])
                       'row 'current-values row-values-shape)
                  tail-compatible
                  (proposition-right
                   (same-shape 'row 'current-values)
                   (compatible 'tail 'current-values)
                   'current-compatible)]
              (app (function/const* 'matrix/compatible-transport [])
                   'tail 'current-values 'row
                   values-row-shape tail-compatible))))]
      (app (matrix-rec motive
                       (function/lam
                        [['current-values vector-type]
                         ['current-compatible
                          (compatible (nil-matrix) 'current-values)]]
                        trivial)
                       step 'rows)
           'values 'rows-compatible)))})

(def composable-inner-compatible-spec
  {:name 'matrix/composable-inner-compatible :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (compatible 'left (column-shape 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (proposition-left
     (compatible 'left (column-shape 'right))
     (rectangular 'right) 'can-compose))})

(def composable-left-rectangular-spec
  {:name 'matrix/composable-left-rectangular :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (rectangular 'left))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (app (function/const* 'matrix/compatible-implies-rectangular [])
         'left (column-shape 'right)
         (app (function/const* 'matrix/composable-inner-compatible [])
              'left 'right 'can-compose)))})

(def composable-right-rectangular-spec
  {:name 'matrix/composable-right-rectangular :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (rectangular 'right))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['can-compose (composable 'left 'right)]]
    (proposition-right
     (compatible 'left (column-shape 'right))
     (rectangular 'right) 'can-compose))})

(def equivalent-column-shape-spec
  {:name 'matrix/equivalent-column-shape :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (same-shape (column-shape 'left) (column-shape 'right)))
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
            (same-shape
             (column-shape 'current-left)
             (column-shape 'current-right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (same-shape
                   (column-shape empty)
                   (column-shape 'current-right))))]
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
                 (same-shape
                  (column-shape empty)
                  (column-shape
                   (cons-matrix 'right-row 'right-tail)))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-shape (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (same-shape
                    (column-shape current-left)
                    (column-shape 'current-right))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (same-shape
                  (column-shape current-left)
                  (column-shape (nil-matrix)))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [tail-same
                       (proposition-right
                        (app (function/const* 'vector/equivalent [])
                             'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)]
                   (conjoin
                    (signed-equivalent signed-zero signed-zero)
                    (same-shape
                     (column-shape 'left-tail)
                     (column-shape 'right-tail))
                    (app
                     (function/const* 'signed/equivalent-reflexive [])
                     signed-zero)
                    (app 'tail-shape 'right-tail tail-same)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def composable-respects-equivalence-spec
  {:name 'matrix/composable-respects-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]
     ['can-compose (composable 'left 'right)]]
    (composable 'equivalent-left 'equivalent-right))
   :value
   (function/lam
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]
     ['can-compose (composable 'left 'right)]]
    (let [inner-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               'left 'right 'can-compose)
          equivalent-left-compatible
          (app
           (function/const*
            'matrix/equivalent-preserves-compatibility [])
           'left 'equivalent-left (column-shape 'right)
           'left-same inner-compatible)
          column-shapes-same
          (app (function/const* 'matrix/equivalent-column-shape [])
               'right 'equivalent-right 'right-same)
          transported-compatible
          (app (function/const* 'matrix/compatible-transport [])
               'equivalent-left
               (column-shape 'right)
               (column-shape 'equivalent-right)
               column-shapes-same equivalent-left-compatible)
          right-rectangular
          (app (function/const* 'matrix/composable-right-rectangular [])
               'left 'right 'can-compose)
          equivalent-right-rectangular
          (app
           (function/const*
            'matrix/equivalent-preserves-rectangularity [])
           'right 'equivalent-right 'right-same right-rectangular)]
      (conjoin
       (compatible 'equivalent-left (column-shape 'equivalent-right))
       (rectangular 'equivalent-right)
       transported-compatible equivalent-right-rectangular)))})

(def definition-specs [composable-spec])
(def theorem-specs
  [compatible-implies-rectangular-spec
   composable-inner-compatible-spec
   composable-left-rectangular-spec
   composable-right-rectangular-spec
   equivalent-column-shape-spec
   composable-respects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      multiply-shape/extend-environment
      (extend-spec-if-missing
       'vector/same-shape-symmetric :vector-shape-cancellation
       vector-shape/same-shape-symmetric-spec)
      (extend-spec-if-missing
       'vector/same-shape-transitive :vector-shape-cancellation
       vector-shape/same-shape-transitive-spec)
      (extend-spec-if-missing
       'matrix/compatible-transport :finite-matrix-shape
       matrix-shape/compatible-transport-spec)
      (extend-spec-if-missing
       'vector/equivalent-implies-same-shape
       :finite-matrix-equivalence-shape
       equivalence-shape/vector-equivalent-implies-same-shape-spec)
      (extend-spec-if-missing
       'matrix/equivalent-preserves-compatibility
       :finite-matrix-equivalence-shape
       equivalence-shape/equivalent-preserves-compatibility-spec)
      (extend-spec-if-missing
       'matrix/equivalent-preserves-rectangularity
       :finite-matrix-equivalence-shape
       equivalence-shape/equivalent-preserves-rectangularity-spec)
      (support/extend-with :finite-matrix-composable
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
