(ns rainbow.math.rational.signed.matrix-lp-duality
  "Signed LP weak duality over native finite matrices and vectors.

  This theorem connects the LP certificate cone to matrix/vector-multiply and
  matrix/transpose.  It is Level-3 mathematical infrastructure: it verifies
  the bound under explicit feasibility, nonnegativity, and shape assumptions;
  it does not connect a Clojure LP implementation to those assumptions."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.action-associative :as associative]
            [rainbow.math.linear.matrix.positive-action :as positive-action]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [t]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & args] (apply function/app f args))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- seqv [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vz [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vle [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- respects [left left* right right* left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left* right right* left-same right-same ordered))
(defn- reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))

(def weak-duality-spec
  (let [row-activity (action 'rows 'x)
        transpose-activity (action (transpose 'rows) 'y)
        primal-objective (dot 'c 'x)
        dual-objective (dot 'b 'y)
        crossing-left (dot transpose-activity 'x)
        crossing-right (dot 'y row-activity)]
    {:name 'optimization/signed-matrix-lp-weak-duality
     :universes []
     :type
     (function/forall
      [['rows matrix-type]
       ['b vector-type] ['c vector-type]
       ['x vector-type] ['y vector-type]
       ['y-row-shape (same-shape 'y (column-shape 'rows))]
       ['rows-x-compatible (compatible 'rows 'x)]
       ['primal-feasible (vle row-activity 'b)]
       ['dual-feasible (vle 'c transpose-activity)]
       ['x-nonnegative (vle (vz 'x) 'x)]
       ['y-nonnegative (vle (vz 'y) 'y)]]
      (sle primal-objective dual-objective))
     :value
     (function/lam
      [['rows matrix-type]
       ['b vector-type] ['c vector-type]
       ['x vector-type] ['y vector-type]
       ['y-row-shape (same-shape 'y (column-shape 'rows))]
       ['rows-x-compatible (compatible 'rows 'x)]
       ['primal-feasible (vle row-activity 'b)]
       ['dual-feasible (vle 'c transpose-activity)]
       ['x-nonnegative (vle (vz 'x) 'x)]
       ['y-nonnegative (vle (vz 'y) 'y)]]
      (let [objective-below-transpose
            (app (function/const* 'vector/dot-left-monotone [])
                 'c transpose-activity 'x
                 'dual-feasible 'x-nonnegative)
            transpose-to-row
            (app (function/const* 'matrix/vector-action-associative [])
                 'rows 'y 'x 'y-row-shape 'rows-x-compatible)
            objective-below-crossing
            (respects
             primal-objective primal-objective
             crossing-left crossing-right
             (reflexive primal-objective)
             transpose-to-row
             objective-below-transpose)
            crossing-below-row-objective
            (app (function/const* 'vector/dot-right-monotone [])
                 'y row-activity 'b
                 'y-nonnegative 'primal-feasible)
            row-to-dual
            (app (function/const* 'vector/dot-commutative []) 'y 'b)
            crossing-below-dual
            (respects
             crossing-right crossing-right
             (dot 'y 'b) dual-objective
             (reflexive crossing-right)
             row-to-dual
             crossing-below-row-objective)]
        (transitive
         primal-objective crossing-right dual-objective
         objective-below-crossing crossing-below-dual)))}))

(def theorem-specs [weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.positive-action])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-matrix-lp-duality theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.matrix-lp-duality))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
