(ns rainbow.math.linear.matrix.affine-bracket-collapse
  "Exact convergence certificates from collapsed affine brackets.

  If residual-certified lower and upper trajectories agree at a finite step,
  nested bracketing forces the lower trajectory to agree with its next step;
  exact stabilization then yields an affine fixed point.  Independently,
  monotonicity shows that every trajectory started between the original
  endpoints agrees with the collapsed value at that step.  Theorem-only,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual-bracket
             :as residual-bracket]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def one (function/app successor zero))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app successor n))
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
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- left [left-prop right-prop evidence]
  (app (function/const* 'proposition/left [])
       left-prop right-prop evidence))
(defn- right [left-prop right-prop evidence]
  (app (function/const* 'proposition/right [])
       left-prop right-prop evidence))
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'vector/equivalent-to-at-most [])
       left right same))
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- at-most-antisymmetric [left right left-right right-left]
  (app (function/const* 'vector/at-most-antisymmetric [])
       left right left-right right-left))

(def affine-iterate-residual-bracket-collapse-stable-spec
  {:name 'matrix/affine-iterate-residual-bracket-collapse-stable
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (veq (iterate-affine 'rows 'offset 'base 'lower)
         (iterate-affine 'rows 'offset (succ 'base) 'lower)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [lower-base (iterate-affine 'rows 'offset 'base 'lower)
          lower-next (iterate-affine 'rows 'offset (succ 'base) 'lower)
          upper-next (iterate-affine 'rows 'offset (succ 'base) 'upper)
          upper-base (iterate-affine 'rows 'offset 'base 'upper)
          lower-grows-prop (vle lower-base lower-next)
          middle-prop (vle lower-next upper-next)
          upper-shrinks-prop (vle upper-next upper-base)
          inner-prop (both middle-prop upper-shrinks-prop)
          nested
          (app
           (function/const*
            'matrix/affine-iterate-residual-nested-bracket [])
           'rows 'offset 'lower 'upper 'rows-positive
           'lower-image-shape 'upper-image-shape
           'lower-residual-upper 'upper-residual-lower
           'lower-upper 'base one)
          lower-grows (left lower-grows-prop inner-prop nested)
          inner (right lower-grows-prop inner-prop nested)
          middle (left middle-prop upper-shrinks-prop inner)
          upper-shrinks (right middle-prop upper-shrinks-prop inner)
          upper-lower
          (equivalent-to-at-most
           upper-base lower-base
           (symmetric lower-base upper-base 'collapsed))
          lower-next-upper-base
          (at-most-transitive
           lower-next upper-next upper-base middle upper-shrinks)
          lower-next-lower-base
          (at-most-transitive
           lower-next upper-base lower-base
           lower-next-upper-base upper-lower)]
      (at-most-antisymmetric
       lower-base lower-next lower-grows lower-next-lower-base)))})

(def affine-iterate-residual-bracket-collapse-fixed-point-spec
  {:name 'matrix/affine-iterate-residual-bracket-collapse-fixed-point
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [value (iterate-affine 'rows 'offset 'base 'lower)]
      (veq (affine 'rows 'offset value) value)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-upper (vle 'lower 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [stable
          (app
           (function/const*
            'matrix/affine-iterate-residual-bracket-collapse-stable [])
           'rows 'offset 'lower 'upper 'rows-positive
           'lower-image-shape 'upper-image-shape
           'lower-residual-upper 'upper-residual-lower
           'lower-upper 'base 'collapsed)]
      (app
       (function/const*
        'matrix/affine-iterate-stable-implies-fixed-point [])
       'rows 'offset 'lower 'base stable)))})

(def affine-iterate-collapsed-bracket-identifies-spec
  {:name 'matrix/affine-iterate-collapsed-bracket-identifies :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['initial vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-initial (vle 'lower 'initial)]
     ['initial-upper (vle 'initial 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (veq (iterate-affine 'rows 'offset 'base 'initial)
         (iterate-affine 'rows 'offset 'base 'lower)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['initial vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-initial (vle 'lower 'initial)]
     ['initial-upper (vle 'initial 'upper)]
     ['base nat]
     ['collapsed
      (veq (iterate-affine 'rows 'offset 'base 'lower)
           (iterate-affine 'rows 'offset 'base 'upper))]]
    (let [lower-at (iterate-affine 'rows 'offset 'base 'lower)
          result (iterate-affine 'rows 'offset 'base 'initial)
          upper-at (iterate-affine 'rows 'offset 'base 'upper)
          lower-result
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'lower 'initial
               'rows-positive 'lower-initial 'base)
          result-upper
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'initial 'upper
               'rows-positive 'initial-upper 'base)
          upper-lower
          (equivalent-to-at-most
           upper-at lower-at
           (symmetric lower-at upper-at 'collapsed))
          result-lower
          (at-most-transitive
           result upper-at lower-at result-upper upper-lower)]
      (at-most-antisymmetric
       result lower-at result-lower lower-result)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-residual-bracket-collapse-stable-spec
   affine-iterate-residual-bracket-collapse-fixed-point-spec
   affine-iterate-collapsed-bracket-identifies-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-bracket])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-bracket-collapse theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-bracket-collapse))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
