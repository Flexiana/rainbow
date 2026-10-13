(ns rainbow.math.linear.matrix.affine-residual-uniqueness
  "Uniqueness of enclosed affine residual solutions after bracket collapse.

  Linear solvers expose `x - rows*x ~ offset`, not an affine fixed-point
  proposition.  Under the exact value/image shape needed to add the image back,
  an enclosed residual solution is identified with a collapsed monotone bracket;
  consequently any two enclosed residual solutions are equivalent.  This is a
  solver-facing corollary of collapsed-bracket fixed-point uniqueness.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-bracket-uniqueness
             :as bracket-uniqueness]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))

(def affine-iterate-collapsed-bracket-identifies-residual-solution-spec
  {:name 'matrix/affine-iterate-collapsed-bracket-identifies-residual-solution
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['candidate vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-candidate (vle 'lower 'candidate)]
     ['candidate-upper (vle 'candidate 'upper)]
     ['candidate-image-shape
      (same-shape 'candidate (action 'rows 'candidate))]
     ['residual-equation
      (veq (vsub 'candidate (action 'rows 'candidate)) 'offset)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (veq 'candidate
         (iterate-affine 'rows 'offset 'base 'lower)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['candidate vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-candidate (vle 'lower 'candidate)]
     ['candidate-upper (vle 'candidate 'upper)]
     ['candidate-image-shape
      (same-shape 'candidate (action 'rows 'candidate))]
     ['residual-equation
      (veq (vsub 'candidate (action 'rows 'candidate)) 'offset)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [fixed
          (app
           (function/const*
            'matrix/affine-residual-equation-implies-fixed-point [])
           'rows 'offset 'candidate 'candidate-image-shape
           'residual-equation)]
      (app
       (function/const*
        'matrix/affine-iterate-collapsed-bracket-identifies-fixed-point [])
       'rows 'offset 'lower 'candidate 'upper
       'rows-positive 'lower-candidate 'candidate-upper fixed
       'base 'collapsed)))})

(def affine-iterate-collapsed-bracket-residual-solutions-equivalent-spec
  {:name 'matrix/affine-iterate-collapsed-bracket-residual-solutions-equivalent
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type]
     ['left-solution vector-type] ['right-solution vector-type]
     ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-left (vle 'lower 'left-solution)]
     ['left-upper (vle 'left-solution 'upper)]
     ['lower-right (vle 'lower 'right-solution)]
     ['right-upper (vle 'right-solution 'upper)]
     ['left-image-shape
      (same-shape 'left-solution (action 'rows 'left-solution))]
     ['right-image-shape
      (same-shape 'right-solution (action 'rows 'right-solution))]
     ['left-residual
      (veq (vsub 'left-solution (action 'rows 'left-solution)) 'offset)]
     ['right-residual
      (veq (vsub 'right-solution (action 'rows 'right-solution)) 'offset)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (veq 'left-solution 'right-solution))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type]
     ['left-solution vector-type] ['right-solution vector-type]
     ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-left (vle 'lower 'left-solution)]
     ['left-upper (vle 'left-solution 'upper)]
     ['lower-right (vle 'lower 'right-solution)]
     ['right-upper (vle 'right-solution 'upper)]
     ['left-image-shape
      (same-shape 'left-solution (action 'rows 'left-solution))]
     ['right-image-shape
      (same-shape 'right-solution (action 'rows 'right-solution))]
     ['left-residual
      (veq (vsub 'left-solution (action 'rows 'left-solution)) 'offset)]
     ['right-residual
      (veq (vsub 'right-solution (action 'rows 'right-solution)) 'offset)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [left-fixed
          (app
           (function/const*
            'matrix/affine-residual-equation-implies-fixed-point [])
           'rows 'offset 'left-solution 'left-image-shape 'left-residual)
          right-fixed
          (app
           (function/const*
            'matrix/affine-residual-equation-implies-fixed-point [])
           'rows 'offset 'right-solution 'right-image-shape 'right-residual)]
      (app
       (function/const*
        'matrix/affine-iterate-collapsed-bracket-fixed-points-equivalent [])
       'rows 'offset 'lower 'left-solution 'right-solution 'upper
       'rows-positive 'lower-left 'left-upper 'lower-right 'right-upper
       left-fixed right-fixed 'base 'collapsed)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-collapsed-bracket-identifies-residual-solution-spec
   affine-iterate-collapsed-bracket-residual-solutions-equivalent-spec])

(defn extend-environment [env]
  (-> env
      bracket-uniqueness/extend-environment
      (support/extend-with :finite-matrix-affine-residual-uniqueness
                           theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
