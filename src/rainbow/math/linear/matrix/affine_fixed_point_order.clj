(ns rainbow.math.linear.matrix.affine-fixed-point-order
  "Order bounds for finite signed affine iteration around a fixed point.

  For a nonnegative matrix, affine action is monotone in its value argument.
  Consequently every finite iterate that starts below a certified fixed point
  remains below it, and every iterate that starts above remains above it.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-equivalence :as equivalence]
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
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-below-fixed-point-spec
  {:name 'matrix/affine-iterate-below-fixed-point :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['fixed-point vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['initial-below (vle 'initial 'fixed-point)]
     ['fixed (veq (affine 'rows 'offset 'fixed-point) 'fixed-point)]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset 'steps 'initial) 'fixed-point))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['fixed-point vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['initial-below (vle 'initial 'fixed-point)]
     ['fixed (veq (affine 'rows 'offset 'fixed-point) 'fixed-point)]
     ['steps nat]]
    (let [initial-at
          (iterate-affine 'rows 'offset 'steps 'initial)
          fixed-at
          (iterate-affine 'rows 'offset 'steps 'fixed-point)
          trajectories-ordered
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'initial 'fixed-point
               'rows-positive 'initial-below 'steps)
          fixed-at-same
          (app (function/const* 'matrix/affine-iterate-fixed-point [])
               'rows 'offset 'fixed-point 'fixed 'steps)
          fixed-at-below
          (app (function/const* 'vector/equivalent-to-at-most [])
               fixed-at 'fixed-point fixed-at-same)]
      (at-most-transitive
       initial-at fixed-at 'fixed-point
       trajectories-ordered fixed-at-below)))})

(def affine-iterate-above-fixed-point-spec
  {:name 'matrix/affine-iterate-above-fixed-point :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['fixed-point vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['initial-above (vle 'fixed-point 'initial)]
     ['fixed (veq (affine 'rows 'offset 'fixed-point) 'fixed-point)]
     ['steps nat]]
    (vle 'fixed-point (iterate-affine 'rows 'offset 'steps 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['fixed-point vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['initial-above (vle 'fixed-point 'initial)]
     ['fixed (veq (affine 'rows 'offset 'fixed-point) 'fixed-point)]
     ['steps nat]]
    (let [fixed-at
          (iterate-affine 'rows 'offset 'steps 'fixed-point)
          initial-at
          (iterate-affine 'rows 'offset 'steps 'initial)
          fixed-at-same
          (app (function/const* 'matrix/affine-iterate-fixed-point [])
               'rows 'offset 'fixed-point 'fixed 'steps)
          fixed-at-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               fixed-at 'fixed-point fixed-at-same)
          fixed-below-fixed-at
          (app (function/const* 'proposition/right [])
               (vle fixed-at 'fixed-point)
               (vle 'fixed-point fixed-at)
               fixed-at-bounds)
          trajectories-ordered
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'fixed-point 'initial
               'rows-positive 'initial-above 'steps)]
      (at-most-transitive
       'fixed-point fixed-at initial-at
       fixed-below-fixed-at trajectories-ordered)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-below-fixed-point-spec
   affine-iterate-above-fixed-point-spec])

(defn extend-environment [env]
  (-> env
      equivalence/extend-environment
      (support/extend-with :finite-matrix-affine-fixed-point-order
                           theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
