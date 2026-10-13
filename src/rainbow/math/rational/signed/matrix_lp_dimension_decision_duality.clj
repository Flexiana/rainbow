(ns rainbow.math.rational.signed.matrix-lp-dimension-decision-duality
  "Signed matrix LP weak duality from executable dimension decisions.

  This is the proof-facing API an independent checker wants: provide evidence
  that the native Nat and matrix dimension deciders returned true, together
  with feasibility and nonnegativity evidence.  The theorem converts those
  decisions into exact length certificates and delegates to the existing
  matrix weak-duality corollary.

  It verifies the submitted decision evidence, not a host parser, solver, or
  arbitrary executable.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.linear.matrix.row-length-decider :as decider]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.linear-order :as nat-order]
            [rainbow.math.rational.signed.matrix-lp-row-length-duality
             :as length-duality]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def true-value (function/const* 'data/true []))

(defn- app [f & args] (apply function/app f args))
(defn- vector-length [values]
  (app (function/const* 'vector/length []) values))
(defn- decide-nat-equality [left right]
  (app (function/const* 'nat/decide-equality []) left right))
(defn- decide-row-length-compatible [rows values]
  (app (function/const* 'matrix/decide-row-length-compatible []) rows values))
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
(defn- bool-equality [left right]
  (function/equality type-level bool left right))

(def weak-duality-from-dimension-decisions-spec
  (let [row-activity (action 'rows 'x)
        transpose-activity (action (transpose 'rows) 'y)
        y-length (vector-length 'y)
        row-count (vector-length (column-shape 'rows))]
    {:name 'optimization/signed-matrix-lp-weak-duality-from-dimension-decisions
     :universes []
     :type
     (function/forall
      [['rows matrix-type]
       ['b vector-type] ['c vector-type]
       ['x vector-type] ['y vector-type]
       ['y-dimension-decision
        (bool-equality
         (decide-nat-equality y-length row-count) true-value)]
       ['rows-x-dimension-decision
        (bool-equality
         (decide-row-length-compatible 'rows 'x) true-value)]
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
       ['y-dimension-decision
        (bool-equality
         (decide-nat-equality y-length row-count) true-value)]
       ['rows-x-dimension-decision
        (bool-equality
         (decide-row-length-compatible 'rows 'x) true-value)]
       ['primal-feasible (vector-at-most row-activity 'b)]
       ['dual-feasible (vector-at-most 'c transpose-activity)]
       ['x-nonnegative (vector-at-most (zero-like 'x) 'x)]
       ['y-nonnegative (vector-at-most (zero-like 'y) 'y)]]
      (let [y-length-certificate
            (app (function/const* 'nat/decide-equality-true-sound [])
                 y-length row-count 'y-dimension-decision)
            rows-x-length-certificate
            (app
             (function/const*
              'matrix/decide-row-length-compatible-true-sound [])
             'rows 'x 'rows-x-dimension-decision)]
        (app
         (function/const*
          'optimization/signed-matrix-lp-weak-duality-from-length-certificates
          [])
         'rows 'b 'c 'x 'y
         y-length-certificate rows-x-length-certificate
         'primal-feasible 'dual-feasible
         'x-nonnegative 'y-nonnegative)))}))

(def theorem-specs [weak-duality-from-dimension-decisions-spec])

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (if (environment/resolve-id current (:name spec))
       current
       (support/extend-with current milestone [spec])))
   checked-environment specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      length-duality/extend-environment
      (extend-specs-if-missing
       :nat-linear-order [nat-order/nat-decide-equality-spec])
      (extend-specs-if-missing
       :boolean-and boolean-and/definition-specs)
      (extend-specs-if-missing
       :boolean-and boolean-and/theorem-specs)
      (extend-specs-if-missing
       :finite-matrix-row-length-decider decider/definition-specs)
      (extend-specs-if-missing
       :finite-matrix-row-length-decider
       [decider/nat-decide-equality-true-sound-spec
        decider/decide-row-length-compatible-true-sound-spec])
      (support/extend-with :signed-matrix-lp-dimension-decision-duality
                           theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
