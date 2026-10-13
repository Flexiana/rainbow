(ns rainbow.math.linear.matrix.affine-residual-order
  "Residual order certificates for affine subsolutions and supersolutions.

  For `F(x) = offset + rows*x`, a Bellman subsolution `x <= F(x)` is
  equivalent to the residual upper bound `x - rows*x <= offset`; dually, a
  supersolution `F(x) <= x` is equivalent to `offset <= x - rows*x`.
  Directional theorems expose the minimal cancellation shape premise and iff
  theorems package both directions.  Theorem-only, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-residual-stopping
             :as residual-stopping]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.linear.vector.subtract-laws :as subtract-laws]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- equivalent-to-at-most [left right same]
  (app (function/const* 'vector/equivalent-to-at-most [])
       left right same))
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- add-right-monotone [left right offset ordered]
  (app (function/const* 'vector/add-right-monotone [])
       left right offset ordered))
(defn- subtract-left-monotone [left right offset ordered]
  (app (function/const* 'vector/subtract-left-monotone [])
       left right offset ordered))

(def affine-subsolution-implies-residual-upper-bound-spec
  {:name 'matrix/affine-subsolution-implies-residual-upper-bound
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['subsolution (vle 'value (affine 'rows 'offset 'value))]]
    (vle (vsub 'value (action 'rows 'value)) 'offset))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['subsolution (vle 'value (affine 'rows 'offset 'value))]]
    (let [image (action 'rows 'value)
          total (vadd 'offset image)
          residual (vsub 'value image)
          total-residual (vsub total image)
          subtract-order
          (subtract-left-monotone 'value total image 'subsolution)
          cancel
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'offset image 'offset-image-shape)
          cancel-order
          (equivalent-to-at-most total-residual 'offset cancel)]
      (at-most-transitive
       residual total-residual 'offset subtract-order cancel-order)))})

(def affine-residual-upper-bound-implies-subsolution-spec
  {:name 'matrix/affine-residual-upper-bound-implies-subsolution
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-upper
      (vle (vsub 'value (action 'rows 'value)) 'offset)]]
    (vle 'value (affine 'rows 'offset 'value)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-upper
      (vle (vsub 'value (action 'rows 'value)) 'offset)]]
    (let [image (action 'rows 'value)
          residual (vsub 'value image)
          recovered (vadd residual image)
          total (vadd 'offset image)
          recover
          (app (function/const* 'vector/subtract-add-right-cancel [])
               'value image 'value-image-shape)
          value-recovered
          (equivalent-to-at-most
           'value recovered (symmetric recovered 'value recover))
          add-order
          (add-right-monotone residual 'offset image 'residual-upper)]
      (at-most-transitive
       'value recovered total value-recovered add-order)))})

(def affine-subsolution-iff-residual-upper-bound-spec
  {:name 'matrix/affine-subsolution-iff-residual-upper-bound
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (proposition/equivalence
     (vle 'value (affine 'rows 'offset 'value))
     (vle (vsub 'value (action 'rows 'value)) 'offset)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (let [subsolution-prop (vle 'value (affine 'rows 'offset 'value))
          residual-prop
          (vle (vsub 'value (action 'rows 'value)) 'offset)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       subsolution-prop residual-prop
       (function/lam
        [['subsolution subsolution-prop]]
        (app
         (function/const*
          'matrix/affine-subsolution-implies-residual-upper-bound [])
         'rows 'offset 'value 'offset-image-shape 'subsolution))
       (function/lam
        [['residual-upper residual-prop]]
        (app
         (function/const*
          'matrix/affine-residual-upper-bound-implies-subsolution [])
         'rows 'offset 'value 'value-image-shape
         'residual-upper)))))})

(def affine-supersolution-implies-residual-lower-bound-spec
  {:name 'matrix/affine-supersolution-implies-residual-lower-bound
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['supersolution (vle (affine 'rows 'offset 'value) 'value)]]
    (vle 'offset (vsub 'value (action 'rows 'value))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['supersolution (vle (affine 'rows 'offset 'value) 'value)]]
    (let [image (action 'rows 'value)
          total (vadd 'offset image)
          total-residual (vsub total image)
          residual (vsub 'value image)
          subtract-order
          (subtract-left-monotone total 'value image 'supersolution)
          cancel
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'offset image 'offset-image-shape)
          offset-total-residual
          (equivalent-to-at-most
           'offset total-residual
           (symmetric total-residual 'offset cancel))]
      (at-most-transitive
       'offset total-residual residual
       offset-total-residual subtract-order)))})

(def affine-residual-lower-bound-implies-supersolution-spec
  {:name 'matrix/affine-residual-lower-bound-implies-supersolution
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-lower
      (vle 'offset (vsub 'value (action 'rows 'value)))]]
    (vle (affine 'rows 'offset 'value) 'value))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]
     ['residual-lower
      (vle 'offset (vsub 'value (action 'rows 'value)))]]
    (let [image (action 'rows 'value)
          residual (vsub 'value image)
          total (vadd 'offset image)
          recovered (vadd residual image)
          add-order
          (add-right-monotone 'offset residual image 'residual-lower)
          recover
          (app (function/const* 'vector/subtract-add-right-cancel [])
               'value image 'value-image-shape)
          recovered-value
          (equivalent-to-at-most recovered 'value recover)]
      (at-most-transitive
       total recovered 'value add-order recovered-value)))})

(def affine-supersolution-iff-residual-lower-bound-spec
  {:name 'matrix/affine-supersolution-iff-residual-lower-bound
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (proposition/equivalence
     (vle (affine 'rows 'offset 'value) 'value)
     (vle 'offset (vsub 'value (action 'rows 'value)))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['offset-image-shape
      (same-shape 'offset (action 'rows 'value))]
     ['value-image-shape
      (same-shape 'value (action 'rows 'value))]]
    (let [supersolution-prop (vle (affine 'rows 'offset 'value) 'value)
          residual-prop
          (vle 'offset (vsub 'value (action 'rows 'value)))]
      (app
       (function/const* 'proposition/equivalence-intro [])
       supersolution-prop residual-prop
       (function/lam
        [['supersolution supersolution-prop]]
        (app
         (function/const*
          'matrix/affine-supersolution-implies-residual-lower-bound [])
         'rows 'offset 'value 'offset-image-shape 'supersolution))
       (function/lam
        [['residual-lower residual-prop]]
        (app
         (function/const*
          'matrix/affine-residual-lower-bound-implies-supersolution [])
         'rows 'offset 'value 'value-image-shape
         'residual-lower)))))})

(def definition-specs [])
(def theorem-specs
  [affine-subsolution-implies-residual-upper-bound-spec
   affine-residual-upper-bound-implies-subsolution-spec
   affine-subsolution-iff-residual-upper-bound-spec
   affine-supersolution-implies-residual-lower-bound-spec
   affine-residual-lower-bound-implies-supersolution-spec
   affine-supersolution-iff-residual-lower-bound-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-stopping])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'vector/subtract-left-monotone :vector-subtract-laws subtract-laws/subtract-left-monotone-spec) (support/extend-with :finite-matrix-affine-residual-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-residual-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
