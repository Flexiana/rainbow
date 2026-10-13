(ns rainbow.math.linear.matrix.affine-bracket-uniqueness
  "Affine fixed-point uniqueness inside a collapsed monotone bracket.

  A fixed point remains equivalent to every finite iterate of itself.  If it
  lies between endpoints whose iterates agree at a finite base step,
  monotonicity identifies that iterate—and therefore the fixed point—with the
  collapsed endpoint.  Applying this twice proves pairwise uniqueness of all
  fixed points in the certified enclosure, without a contraction assumption.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-bracket-collapse
             :as bracket-collapse]
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
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-collapsed-bracket-identifies-fixed-point-spec
  {:name 'matrix/affine-iterate-collapsed-bracket-identifies-fixed-point
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['candidate vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-candidate (vle 'lower 'candidate)]
     ['candidate-upper (vle 'candidate 'upper)]
     ['fixed (veq (affine 'rows 'offset 'candidate) 'candidate)]
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
     ['fixed (veq (affine 'rows 'offset 'candidate) 'candidate)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [candidate-at
          (iterate-affine 'rows 'offset 'base 'candidate)
          lower-at
          (iterate-affine 'rows 'offset 'base 'lower)
          candidate-at-fixed
          (app (function/const* 'matrix/affine-iterate-fixed-point [])
               'rows 'offset 'candidate 'fixed 'base)
          candidate-fixed-at
          (symmetric candidate-at 'candidate candidate-at-fixed)
          identified
          (app
           (function/const*
            'matrix/affine-iterate-collapsed-bracket-identifies [])
           'rows 'offset 'lower 'candidate 'upper
           'rows-positive 'lower-candidate 'candidate-upper
           'base 'collapsed)]
      (transitive
       'candidate candidate-at lower-at
       candidate-fixed-at identified)))})

(def affine-iterate-collapsed-bracket-fixed-points-equivalent-spec
  {:name 'matrix/affine-iterate-collapsed-bracket-fixed-points-equivalent
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type]
     ['left-fixed-point vector-type] ['right-fixed-point vector-type]
     ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-left (vle 'lower 'left-fixed-point)]
     ['left-upper (vle 'left-fixed-point 'upper)]
     ['lower-right (vle 'lower 'right-fixed-point)]
     ['right-upper (vle 'right-fixed-point 'upper)]
     ['left-fixed
      (veq (affine 'rows 'offset 'left-fixed-point) 'left-fixed-point)]
     ['right-fixed
      (veq (affine 'rows 'offset 'right-fixed-point) 'right-fixed-point)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (veq 'left-fixed-point 'right-fixed-point))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type]
     ['left-fixed-point vector-type] ['right-fixed-point vector-type]
     ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-left (vle 'lower 'left-fixed-point)]
     ['left-upper (vle 'left-fixed-point 'upper)]
     ['lower-right (vle 'lower 'right-fixed-point)]
     ['right-upper (vle 'right-fixed-point 'upper)]
     ['left-fixed
      (veq (affine 'rows 'offset 'left-fixed-point) 'left-fixed-point)]
     ['right-fixed
      (veq (affine 'rows 'offset 'right-fixed-point) 'right-fixed-point)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [collapsed-value
          (iterate-affine 'rows 'offset 'base 'lower)
          left-collapsed
          (app
           (function/const*
            'matrix/affine-iterate-collapsed-bracket-identifies-fixed-point [])
           'rows 'offset 'lower 'left-fixed-point 'upper
           'rows-positive 'lower-left 'left-upper 'left-fixed
           'base 'collapsed)
          right-collapsed
          (app
           (function/const*
            'matrix/affine-iterate-collapsed-bracket-identifies-fixed-point [])
           'rows 'offset 'lower 'right-fixed-point 'upper
           'rows-positive 'lower-right 'right-upper 'right-fixed
           'base 'collapsed)
          collapsed-right
          (symmetric 'right-fixed-point collapsed-value right-collapsed)]
      (transitive
       'left-fixed-point collapsed-value 'right-fixed-point
       left-collapsed collapsed-right)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-collapsed-bracket-identifies-fixed-point-spec
   affine-iterate-collapsed-bracket-fixed-points-equivalent-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-bracket-collapse])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-bracket-uniqueness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-bracket-uniqueness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
