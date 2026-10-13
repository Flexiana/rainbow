(ns rainbow.math.rational.signed.matrix-lp-row-length-duality
  "Signed matrix LP weak duality from concrete dimension certificates.

  The core theorem accepts abstract `same-shape` and `matrix/compatible`
  evidence.  External checkers naturally measure lengths instead.  This
  corollary accepts exact length equality for the dual vector and one row-length
  equality per constraint row, derives the abstract premises, and delegates the
  actual optimization argument to the existing weak-duality theorem.

  This changes the certificate boundary, not the mathematical guarantee.  It is
  Level-3, native, deterministic, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.row-length-shape :as row-length]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.matrix-lp-duality :as matrix-lp]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & args] (apply function/app f args))
(defn- vector-length [values]
  (app (function/const* 'vector/length []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- row-length-compatible [rows values]
  (app (function/const* 'matrix/row-length-compatible []) rows values))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- column-shape [rows]
  (app (function/const* 'matrix/column-shape []) rows))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(def weak-duality-from-length-certificates-spec
  (let [row-activity (action 'rows 'x)
        transpose-activity (action (transpose 'rows) 'y)]
    {:name 'optimization/signed-matrix-lp-weak-duality-from-length-certificates
     :universes []
     :type
     (function/forall
      [['rows matrix-type]
       ['b vector-type] ['c vector-type]
       ['x vector-type] ['y vector-type]
       ['y-row-length
        (nat-equality (vector-length 'y)
                      (vector-length (column-shape 'rows)))]
       ['rows-x-lengths (row-length-compatible 'rows 'x)]
       ['primal-feasible (vector-at-most row-activity 'b)]
       ['dual-feasible (vector-at-most 'c transpose-activity)]
       ['x-nonnegative (vector-at-most (zero-like 'x) 'x)]
       ['y-nonnegative (vector-at-most (zero-like 'y) 'y)]]
      (signed-at-most (dot 'c 'x) (dot 'b 'y)))
     :value
     (function/lam
      [['rows matrix-type]
       ['b vector-type] ['c vector-type]
       ['x vector-type] ['y vector-type]
       ['y-row-length
        (nat-equality (vector-length 'y)
                      (vector-length (column-shape 'rows)))]
       ['rows-x-lengths (row-length-compatible 'rows 'x)]
       ['primal-feasible (vector-at-most row-activity 'b)]
       ['dual-feasible (vector-at-most 'c transpose-activity)]
       ['x-nonnegative (vector-at-most (zero-like 'x) 'x)]
       ['y-nonnegative (vector-at-most (zero-like 'y) 'y)]]
      (let [y-row-shape
            (app
             (function/const*
              'vector/length-equality-implies-same-shape [])
             'y (column-shape 'rows) 'y-row-length)
            rows-x-compatible
            (app
             (function/const*
              'matrix/row-length-compatible-implies-compatible [])
             'rows 'x 'rows-x-lengths)]
        (app
         (function/const* 'optimization/signed-matrix-lp-weak-duality [])
         'rows 'b 'c 'x 'y
         y-row-shape rows-x-compatible
         'primal-feasible 'dual-feasible
         'x-nonnegative 'y-nonnegative)))}))

(def theorem-specs [weak-duality-from-length-certificates-spec])

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (if (environment/resolve-id current (:name spec))
       current
       (support/extend-with current milestone [spec])))
   checked-environment specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.matrix-lp-duality])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-specs-if-missing :finite-matrix-row-length-shape row-length/definition-specs) (extend-specs-if-missing :finite-matrix-row-length-shape [row-length/length-equality-implies-same-shape-spec row-length/row-length-compatible-implies-compatible-spec]) (support/extend-with :signed-matrix-lp-row-length-duality theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.matrix-lp-row-length-duality))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
