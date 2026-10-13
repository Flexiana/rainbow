(ns rainbow.math.linear.matrix.affine-approximate-offset-stability
  "Robust stability for approximate solutions under offset perturbation.

  For the same nonnegative contractive rows, let x approximately solve
  `x = b + A*x` and y approximately solve `y = c + A*y`.  Then

      d(x,y) <= 2 * (d(x,b+A*x) + (d(b,c) + d(c+A*y,y))).

  Thus disagreement is controlled jointly by the two independently checkable
  solver residuals and the input/reward perturbation.  The threshold theorem
  accepts a separate bound for each contribution.  No exact fixed point is
  assumed.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-approximate-stability
             :as approximate-stability]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-translation :as translation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- row-sums-bounded [rows gamma]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) (from-nnrat gamma))))
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- add-monotone [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-monotone [])
       left left-prime right right-prime first second))
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- robust-binders []
  (let [left-image (affine-action 'rows 'left-offset 'left)
        right-image (affine-action 'rows 'right-offset 'right)]
    [['rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left vector-type] ['right vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['left-offset-shape
      (same-shape 'left-offset (action 'rows 'left))]
     ['right-offset-shape
      (same-shape 'right-offset (action 'rows 'right))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'gamma)]]))

(defn- right-residual-under-left-offset
  [right-action left-offset-right-shape
   common-image right-image right-residual
   offset-image-distance offset-distance]
  (let [common-image-left-offset-shape
        (app
         (function/const* 'vector/add-preserves-left-shape [])
         'left-offset right-action left-offset-right-shape)
        right-image-right-offset-shape
        (app
         (function/const* 'vector/add-preserves-left-shape [])
         'right-offset right-action 'right-offset-shape)
        offset-shape
        (shape-transitive
         'left-offset right-action 'right-offset
         left-offset-right-shape
         (shape-symmetric
          'right-offset right-action 'right-offset-shape))
        common-right-image-shape
        (shape-transitive
         common-image 'left-offset right-image
         common-image-left-offset-shape
         (shape-transitive
          'left-offset 'right-offset right-image
          offset-shape
          (shape-symmetric
           right-image 'right-offset right-image-right-offset-shape)))
        common-right-shape
        (shape-transitive
         common-image right-image 'right
         common-right-image-shape 'right-residual-shape)
        triangle
        (app
         (function/const* 'vector/sup-distance-triangle-same-shape [])
         common-image right-image 'right
         common-right-image-shape 'right-residual-shape)
        translation-same
        (app
         (function/const* 'vector/sup-distance-add-right-same-shape [])
         'left-offset 'right-offset right-action
         (shape-symmetric
          'left-offset right-action left-offset-right-shape)
         (shape-symmetric
          'right-offset right-action 'right-offset-shape))
        offset-bound
        (app (function/const* 'signed/equivalent-to-at-most [])
             offset-image-distance offset-distance translation-same)
        sum-bound
        (add-monotone
         offset-image-distance offset-distance
         right-residual right-residual
         offset-bound (order-reflexive right-residual))]
    {:shape common-right-shape
     :bound
     (order-transitive
      (sup-distance common-image 'right)
      (sadd offset-image-distance right-residual)
      (sadd offset-distance right-residual)
      triangle sum-bound)}))

(def affine-nnrat-approximate-offset-stability-spec
  (let [right-action (action 'rows 'right)
        left-image (affine-action 'rows 'left-offset 'left)
        common-image (affine-action 'rows 'left-offset 'right)
        right-image (affine-action 'rows 'right-offset 'right)
        left-residual (sup-distance 'left left-image)
        right-residual (sup-distance right-image 'right)
        offset-image-distance (sup-distance common-image right-image)
        offset-distance (sup-distance 'left-offset 'right-offset)
        aggregate (sadd left-residual (sadd offset-distance right-residual))]
    {:name 'matrix/affine-nnrat-approximate-offset-stability
     :universes []
     :type
     (function/forall
      (robust-binders)
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      (robust-binders)
      (let [right-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'rows 'left 'right)
            left-offset-right-shape
            (shape-transitive
             'left-offset (action 'rows 'left) right-action
             'left-offset-shape right-action-shape)
            transported
            (right-residual-under-left-offset
             right-action left-offset-right-shape
             common-image right-image right-residual
             offset-image-distance offset-distance)]
        (app
         (function/const*
          'matrix/affine-nnrat-two-threshold-stability-certificate [])
         'rows 'left-offset 'left 'right
         'gamma 'gamma-at-most-half
         'shape 'left-residual-shape (:shape transported)
         'left-offset-shape 'positive-rows 'bounded-sums
         left-residual (sadd offset-distance right-residual)
         (order-reflexive left-residual) (:bound transported))))}))

(def affine-nnrat-approximate-offset-threshold-stability-spec
  (let [left-image (affine-action 'rows 'left-offset 'left)
        right-image (affine-action 'rows 'right-offset 'right)
        left-residual (sup-distance 'left left-image)
        right-residual (sup-distance right-image 'right)
        offset-distance (sup-distance 'left-offset 'right-offset)
        aggregate (sadd left-residual (sadd offset-distance right-residual))
        threshold-aggregate
        (sadd 'left-threshold
              (sadd 'offset-threshold 'right-threshold))
        binders
        (into
         (robust-binders)
         [['left-threshold signed]
          ['offset-threshold signed]
          ['right-threshold signed]
          ['left-residual-bound (sle left-residual 'left-threshold)]
          ['offset-distance-bound
           (sle offset-distance 'offset-threshold)]
          ['right-residual-bound
           (sle right-residual 'right-threshold)]])]
    {:name 'matrix/affine-nnrat-approximate-offset-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (sadd threshold-aggregate threshold-aggregate)))
     :value
     (function/lam
      binders
      (let [robust-bound
            (app
             (function/const*
              'matrix/affine-nnrat-approximate-offset-stability [])
             'rows 'left-offset 'right-offset 'left 'right
             'gamma 'gamma-at-most-half
             'shape 'left-residual-shape 'right-residual-shape
             'left-offset-shape 'right-offset-shape
             'positive-rows 'bounded-sums)
            right-pair-bound
            (add-monotone
             offset-distance 'offset-threshold
             right-residual 'right-threshold
             'offset-distance-bound 'right-residual-bound)
            aggregate-bound
            (add-monotone
             left-residual 'left-threshold
             (sadd offset-distance right-residual)
             (sadd 'offset-threshold 'right-threshold)
             'left-residual-bound right-pair-bound)
            doubled-bound
            (add-monotone
             aggregate threshold-aggregate aggregate threshold-aggregate
             aggregate-bound aggregate-bound)]
        (order-transitive
         (sup-distance 'left 'right)
         (sadd aggregate aggregate)
         (sadd threshold-aggregate threshold-aggregate)
         robust-bound doubled-bound)))}))

(def definition-specs [])
(def theorem-specs
  [affine-nnrat-approximate-offset-stability-spec
   affine-nnrat-approximate-offset-threshold-stability-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-approximate-stability])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :signed-vector-sup-translation translation/theorem-specs) (support/extend-with :finite-matrix-affine-approximate-offset-stability theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-approximate-offset-stability))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
