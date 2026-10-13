(ns rainbow.math.linear.matrix.shape
  "Explicit width and rectangularity certificates for nested-List matrices.

    matrix/compatible rows values
      says every row has the same shape as `values`.

    matrix/rectangular rows
      is true for the empty matrix and, for a nonempty matrix, says every tail
      row has the same shape as the head row.

  The accompanying laws expose constructor/destructor APIs, transport
  compatibility across vector shape equality, show rectangularity is inherited
  by matrix tails, and recover compatibility with the first row.  These types
  make raggedness explicit before transpose or matrix composition is added.
  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.matrix :as matrix]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def truth (function/const* 'proposition/truth []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def compatible-spec
  {:name 'matrix/compatible :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type 'Prop)
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      vector-type
      (function/lam
       [['ignored matrix-type]]
       (function/arrow vector-type 'Prop))
      (function/lam [['ignored-values vector-type]] truth)
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['tail-compatible (function/arrow vector-type 'Prop)]]
       (function/lam
        [['current-values vector-type]]
        (conjunction
         (same-shape 'row 'current-values)
         (app 'tail-compatible 'current-values))))
      'rows)
     'values))})

(def rectangular-spec
  {:name 'matrix/rectangular :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type 'Prop)
   :value
   (function/lam
    [['rows matrix-type]]
    (app
     (function/const* 'data/List.rec [type-level type-level])
     vector-type
     (function/lam [['ignored matrix-type]] 'Prop)
     truth
     (function/lam
      [['row vector-type] ['tail matrix-type] ['ignored 'Prop]]
      (compatible 'tail 'row))
     'rows))})

(def compatible-nil-spec
  {:name 'matrix/compatible-nil :universes []
   :type
   (function/forall
    [['values vector-type]]
    (compatible (nil-matrix) 'values))
   :value
   (function/lam [['values vector-type]] trivial)})

(def compatible-cons-spec
  {:name 'matrix/compatible-cons :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['head-shape (same-shape 'row 'values)]
     ['tail-compatible (compatible 'tail 'values)]]
    (compatible (cons-matrix 'row 'tail) 'values))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['head-shape (same-shape 'row 'values)]
     ['tail-compatible (compatible 'tail 'values)]]
    (conjoin
     (same-shape 'row 'values)
     (compatible 'tail 'values)
     'head-shape 'tail-compatible))})

(def compatible-head-shape-spec
  {:name 'matrix/compatible-head-shape :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (same-shape 'row 'values))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (proposition-left
     (same-shape 'row 'values)
     (compatible 'tail 'values)
     'rows-compatible))})

(def compatible-tail-spec
  {:name 'matrix/compatible-tail :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (compatible 'tail 'values))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['values vector-type]
     ['rows-compatible
      (compatible (cons-matrix 'row 'tail) 'values)]]
    (proposition-right
     (same-shape 'row 'values)
     (compatible 'tail 'values)
     'rows-compatible))})

(def compatible-transport-spec
  {:name 'matrix/compatible-transport :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['reference-shape (same-shape 'left 'right)]
     ['left-compatible (compatible 'rows 'left)]]
    (compatible 'rows 'right))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['reference-shape (same-shape 'left 'right)]
     ['left-compatible (compatible 'rows 'left)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/forall
            [['current-left vector-type] ['current-right vector-type]
             ['current-reference-shape
              (same-shape 'current-left 'current-right)]
             ['current-compatible
              (compatible 'current-rows 'current-left)]]
            (compatible 'current-rows 'current-right)))
          base
          (function/lam
           [['current-left vector-type] ['current-right vector-type]
            ['current-reference-shape
             (same-shape 'current-left 'current-right)]
            ['current-compatible
             (compatible (nil-matrix) 'current-left)]]
           trivial)
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-transport (app motive 'tail)]]
           (function/lam
            [['current-left vector-type] ['current-right vector-type]
             ['current-reference-shape
              (same-shape 'current-left 'current-right)]
             ['current-compatible
              (compatible
               (cons-matrix 'row 'tail) 'current-left)]]
            (let [row-left
                  (proposition-left
                   (same-shape 'row 'current-left)
                   (compatible 'tail 'current-left)
                   'current-compatible)
                  tail-left
                  (proposition-right
                   (same-shape 'row 'current-left)
                   (compatible 'tail 'current-left)
                   'current-compatible)
                  row-right
                  (app (function/const* 'vector/same-shape-transitive [])
                       'row 'current-left 'current-right
                       row-left 'current-reference-shape)
                  tail-right
                  (app 'tail-transport
                       'current-left 'current-right
                       'current-reference-shape tail-left)]
              (conjoin
               (same-shape 'row 'current-right)
               (compatible 'tail 'current-right)
               row-right tail-right))))]
      (app (matrix-rec motive base step 'rows)
           'left 'right 'reference-shape 'left-compatible)))})

(def rectangular-tail-spec
  {:name 'matrix/rectangular-tail :universes []
   :type
   (function/forall
    [['head vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cons-matrix 'head 'tail))]]
    (rectangular 'tail))
   :value
   (function/lam
    [['head vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cons-matrix 'head 'tail))]]
    (let [motive
          (function/lam
           [['current-tail matrix-type]]
           (function/arrow
            (rectangular (cons-matrix 'head 'current-tail))
            (rectangular 'current-tail)))
          base
          (function/lam
           [['current-rectangular
             (rectangular (cons-matrix 'head (nil-matrix)))]]
           trivial)
          step
          (function/lam
           [['second vector-type] ['rest matrix-type]
            ['ignored (app motive 'rest)]]
           (function/lam
            [['current-rectangular
              (rectangular
               (cons-matrix
                'head (cons-matrix 'second 'rest)))]]
            (let [second-head
                  (proposition-left
                   (same-shape 'second 'head)
                   (compatible 'rest 'head)
                   'current-rectangular)
                  rest-head
                  (proposition-right
                   (same-shape 'second 'head)
                   (compatible 'rest 'head)
                   'current-rectangular)
                  head-second
                  (app (function/const* 'vector/same-shape-symmetric [])
                       'second 'head second-head)]
              (app (function/const* 'matrix/compatible-transport [])
                   'rest 'head 'second head-second rest-head))))]
      (app (matrix-rec motive base step 'tail)
           'rows-rectangular)))})

(def compatible-with-head-of-rectangular-spec
  {:name 'matrix/compatible-with-head-of-rectangular :universes []
   :type
   (function/forall
    [['head vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cons-matrix 'head 'tail))]]
    (compatible (cons-matrix 'head 'tail) 'head))
   :value
   (function/lam
    [['head vector-type] ['tail matrix-type]
     ['rows-rectangular
      (rectangular (cons-matrix 'head 'tail))]]
    (conjoin
     (same-shape 'head 'head)
     (compatible 'tail 'head)
     (app (function/const* 'vector/same-shape-reflexive []) 'head)
     'rows-rectangular))})

(def definition-specs [compatible-spec rectangular-spec])
(def theorem-specs
  [compatible-nil-spec
   compatible-cons-spec
   compatible-head-shape-spec
   compatible-tail-spec
   compatible-transport-spec
   rectangular-tail-spec
   compatible-with-head-of-rectangular-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      matrix/extend-environment
      (extend-spec-if-missing
       'vector/same-shape-reflexive :vector-shape-cancellation
       shape/same-shape-reflexive-spec)
      (extend-spec-if-missing
       'vector/same-shape-symmetric :vector-shape-cancellation
       shape/same-shape-symmetric-spec)
      (extend-spec-if-missing
       'vector/same-shape-transitive :vector-shape-cancellation
       shape/same-shape-transitive-spec)
      (support/extend-with :finite-matrix-shape
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
