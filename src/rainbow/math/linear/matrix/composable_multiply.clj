(ns rainbow.math.linear.matrix.composable-multiply
  "Closure of matrix composability under native multiplication bracketings.

  Row count of B*C equals row count of B, and B*C is always rectangular, so
  A composable B implies A composable (B*C).  Conversely, when B is explicitly
  nonempty, B composable C fixes B's column width to C's row count; output-shape
  laws then show (A*B) composable C.  The combined theorem certifies both sides
  of an associative triple without claiming their values equal yet.  Native
  and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.composable :as composability]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
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

(defn- app [f & args] (apply function/app f args))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
(defn- composable [left right]
  (app (function/const* 'matrix/composable []) left right))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def composable-with-product-right-spec
  {:name 'matrix/composable-with-product-right :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle-composable (composable 'left 'middle)]]
    (composable 'left (multiply 'middle 'right)))
   :value
   (function/lam
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle-composable (composable 'left 'middle)]]
    (let [left-middle-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               'left 'middle 'left-middle-composable)
          product-middle-shape
          (app (function/const* 'matrix/multiply-left-column-shape [])
               'middle 'right)
          middle-product-shape
          (app (function/const* 'vector/same-shape-symmetric [])
               (column-shape (multiply 'middle 'right))
               (column-shape 'middle) product-middle-shape)
          left-product-compatible
          (app (function/const* 'matrix/compatible-transport [])
               'left (column-shape 'middle)
               (column-shape (multiply 'middle 'right))
               middle-product-shape left-middle-compatible)
          product-rectangular
          (app (function/const* 'matrix/multiply-rectangular [])
               'middle 'right)]
      (conjoin
       (compatible 'left (column-shape (multiply 'middle 'right)))
       (rectangular (multiply 'middle 'right))
       left-product-compatible product-rectangular)))})

(def product-left-composable-spec
  {:name 'matrix/product-left-composable :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (composable
     (multiply
      'left (cons-matrix 'middle-head 'middle-tail))
     'right))
   :value
   (function/lam
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (let [middle (cons-matrix 'middle-head 'middle-tail)
          product-reference
          (vector-multiply (transpose middle) 'middle-head)
          product-compatible
          (app
           (function/const*
            'matrix/multiply-compatible-with-row-image [])
           'left middle 'middle-head)
          reference-transpose-shape
          (app
           (function/const* 'matrix/vector-multiply-column-shape [])
           (transpose middle) 'middle-head)
          transpose-head-shape
          (app
           (function/const* 'matrix/prepend-column-output-shape [])
           'middle-head (transpose 'middle-tail))
          middle-right-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               middle 'right 'middle-right-composable)
          middle-head-right-shape
          (app (function/const* 'matrix/compatible-head-shape [])
               'middle-head 'middle-tail (column-shape 'right)
               middle-right-compatible)
          reference-head-shape
          (app (function/const* 'vector/same-shape-transitive [])
               product-reference (column-shape (transpose middle))
               'middle-head
               reference-transpose-shape transpose-head-shape)
          reference-right-shape
          (app (function/const* 'vector/same-shape-transitive [])
               product-reference 'middle-head (column-shape 'right)
               reference-head-shape middle-head-right-shape)
          product-right-compatible
          (app (function/const* 'matrix/compatible-transport [])
               (multiply 'left middle)
               product-reference (column-shape 'right)
               reference-right-shape product-compatible)
          right-rectangular
          (app (function/const* 'matrix/composable-right-rectangular [])
               middle 'right 'middle-right-composable)]
      (conjoin
       (compatible (multiply 'left middle) (column-shape 'right))
       (rectangular 'right)
       product-right-compatible right-rectangular)))})

(def composable-bracketings-spec
  {:name 'matrix/composable-bracketings :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['left-middle-composable
      (composable
       'left (cons-matrix 'middle-head 'middle-tail))]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (conjunction
     (composable
      (multiply
       'left (cons-matrix 'middle-head 'middle-tail))
      'right)
     (composable
      'left
      (multiply
       (cons-matrix 'middle-head 'middle-tail) 'right))))
   :value
   (function/lam
    [['left matrix-type] ['middle-head vector-type]
     ['middle-tail matrix-type] ['right matrix-type]
     ['left-middle-composable
      (composable
       'left (cons-matrix 'middle-head 'middle-tail))]
     ['middle-right-composable
      (composable
       (cons-matrix 'middle-head 'middle-tail) 'right)]]
    (conjoin
     (composable
      (multiply
       'left (cons-matrix 'middle-head 'middle-tail))
      'right)
     (composable
      'left
      (multiply
       (cons-matrix 'middle-head 'middle-tail) 'right))
     (app (function/const* 'matrix/product-left-composable [])
          'left 'middle-head 'middle-tail 'right
          'middle-right-composable)
     (app (function/const* 'matrix/composable-with-product-right [])
          'left (cons-matrix 'middle-head 'middle-tail) 'right
          'left-middle-composable)))})

(def definition-specs [])
(def theorem-specs
  [composable-with-product-right-spec
   product-left-composable-spec
   composable-bracketings-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.composable])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'matrix/compatible-head-shape :finite-matrix-shape matrix-shape/compatible-head-shape-spec) (extend-spec-if-missing 'matrix/prepend-column-output-shape :finite-matrix-transpose-shape transpose-shape/prepend-column-output-shape-spec) (support/extend-with :finite-matrix-composable-multiply theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.composable-multiply))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
