(ns rainbow.math.linear.matrix.affine-residual
  "Shape-safe residual characterization of affine fixed points.

  For `F(x) = offset + rows*x`, the Bellman fixed-point equation `F(x) ~ x`
  is equivalent to the linear residual equation `x - rows*x ~ offset` when the
  involved vectors have the shapes required by truncating vector arithmetic.
  The two directions expose their minimal shape premises; the iff theorem
  packages both.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-stabilization
             :as stabilization]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.linear.vector.shape-cancellation :as shape-cancellation]
            [rainbow.math.linear.vector.subtract-laws :as subtract-laws]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- reflexive [values]
  (app (function/const* 'vector/equivalent-reflexive []) values))
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right left-middle middle-right))

(def affine-fixed-point-implies-residual-equation-spec
  {:name 'matrix/affine-fixed-point-implies-residual-equation :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['fixed (veq (affine 'rows 'offset 'value) 'value)]]
    (veq (vsub 'value (action 'rows 'value)) 'offset))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['fixed (veq (affine 'rows 'offset 'value) 'value)]]
    (let [image (action 'rows 'value)
          total (vadd 'offset image)
          total-residual (vsub total image)
          residual (vsub 'value image)
          transported
          (app (function/const* 'vector/subtract-respects-equivalence [])
               total 'value image image 'fixed (reflexive image))
          cancelled
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'offset image 'offset-image-shape)]
      (transitive
       residual total-residual 'offset
       (symmetric total-residual residual transported)
       cancelled)))})

(def affine-residual-equation-implies-fixed-point-spec
  {:name 'matrix/affine-residual-equation-implies-fixed-point :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-equation
      (veq (vsub 'value (action 'rows 'value)) 'offset)]]
    (veq (affine 'rows 'offset 'value) 'value))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-equation
      (veq (vsub 'value (action 'rows 'value)) 'offset)]]
    (let [image (action 'rows 'value)
          residual (vsub 'value image)
          recovered (vadd residual image)
          total (vadd 'offset image)
          align
          (app (function/const* 'vector/add-respects-equivalence [])
               residual 'offset image image
               'residual-equation (reflexive image))
          cancel
          (app (function/const* 'vector/subtract-add-right-cancel [])
               'value image 'value-image-shape)]
      (transitive
       total recovered 'value
       (symmetric recovered total align)
       cancel)))})

(def affine-fixed-point-iff-residual-equation-spec
  {:name 'matrix/affine-fixed-point-iff-residual-equation :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (proposition/equivalence
     (veq (affine 'rows 'offset 'value) 'value)
     (veq (vsub 'value (action 'rows 'value)) 'offset)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (let [fixed-prop (veq (affine 'rows 'offset 'value) 'value)
          residual-prop
          (veq (vsub 'value (action 'rows 'value)) 'offset)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       fixed-prop residual-prop
       (function/lam
        [['fixed fixed-prop]]
        (app
         (function/const*
          'matrix/affine-fixed-point-implies-residual-equation [])
         'rows 'offset 'value 'offset-image-shape 'fixed))
       (function/lam
        [['residual-equation residual-prop]]
        (app
         (function/const*
          'matrix/affine-residual-equation-implies-fixed-point [])
         'rows 'offset 'value 'value-image-shape
         'residual-equation)))))})

(def definition-specs [])
(def theorem-specs
  [affine-fixed-point-implies-residual-equation-spec
   affine-residual-equation-implies-fixed-point-spec
   affine-fixed-point-iff-residual-equation-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      stabilization/extend-environment
      (extend-spec-if-missing
       'vector/add-subtract-right-cancel
       :vector-shape-cancellation
       shape-cancellation/add-subtract-right-cancel-spec)
      (extend-spec-if-missing
       'vector/subtract-respects-equivalence
       :vector-subtract-laws
       subtract-laws/subtract-respects-equivalence-spec)
      (support/extend-with :finite-matrix-affine-residual theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
