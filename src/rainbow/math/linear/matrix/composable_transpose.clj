(ns rainbow.math.linear.matrix.composable-transpose
  "Composable native matrix pairs reverse under transpose.

  If a nonempty matrix A composes with B, then transpose B composes with
  transpose A.  Nonemptiness supplies A's row width as the row count of its
  transpose; zero-width rows remain valid.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.transpose-multiply-reverse :as reverse]
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
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- same-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(def composable-transpose-reverse-spec
  {:name 'matrix/composable-transpose-reverse-nonempty-left :universes []
   :type
   (function/forall
    [['left-head vector-type] ['left-tail matrix-type]
     ['right matrix-type]
     ['can-compose
      (composable (cons-matrix 'left-head 'left-tail) 'right)]]
    (composable
     (transpose 'right)
     (transpose (cons-matrix 'left-head 'left-tail))))
   :value
   (function/lam
    [['left-head vector-type] ['left-tail matrix-type]
     ['right matrix-type]
     ['can-compose
      (composable (cons-matrix 'left-head 'left-tail) 'right)]]
    (let [left (cons-matrix 'left-head 'left-tail)
          left-inner-compatible
          (app (function/const* 'matrix/composable-inner-compatible [])
               left 'right 'can-compose)
          left-head-width
          (app (function/const* 'matrix/compatible-head-shape [])
               'left-head 'left-tail (column-shape 'right)
               left-inner-compatible)
          right-column-head-shape
          (same-shape-symmetric
           'left-head (column-shape 'right) left-head-width)
          transpose-left-output-shape
          (app (function/const* 'matrix/prepend-column-output-shape [])
               'left-head (transpose 'left-tail))
          head-transpose-left-shape
          (same-shape-symmetric
           (column-shape (transpose left)) 'left-head
           transpose-left-output-shape)
          reference-shape
          (same-shape-transitive
           (column-shape 'right) 'left-head
           (column-shape (transpose left))
           right-column-head-shape head-transpose-left-shape)
          right-rectangular
          (app (function/const* 'matrix/composable-right-rectangular [])
               left 'right 'can-compose)
          transpose-right-reference
          (app
           (function/const*
            'matrix/transpose-compatible-column-shape [])
           'right right-rectangular)
          transpose-right-inner
          (app (function/const* 'matrix/compatible-transport [])
               (transpose 'right)
               (column-shape 'right)
               (column-shape (transpose left))
               reference-shape transpose-right-reference)
          left-rectangular
          (app (function/const* 'matrix/composable-left-rectangular [])
               left 'right 'can-compose)
          transpose-left-rectangular
          (app (function/const* 'matrix/transpose-preserves-rectangularity [])
               left left-rectangular)]
      (conjoin
       (compatible
        (transpose 'right) (column-shape (transpose left)))
       (rectangular (transpose left))
       transpose-right-inner transpose-left-rectangular)))})

(def definition-specs [])
(def theorem-specs [composable-transpose-reverse-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose-multiply-reverse])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-composable-transpose theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.composable-transpose))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
