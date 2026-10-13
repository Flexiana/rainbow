(ns rainbow.math.linear.matrix.affine-operator-sensitivity
  "Approximate-solution stability across certified affine-map perturbations.

  A reusable bridge theorem compares an approximate solution x of a
  contractive affine map F with a point y certified against any comparison
  image G(y).  A bound on d(F(y),G(y)) converts the comparison certificate into
  an F-residual and yields

      d(x,y) <= 2 * (residual-x + (bridge + residual-y)).

  The row-perturbation specialization takes F(y)=b+A*y and G(y)=b+B*y, reducing
  the bridge exactly to d(A*y,B*y).  This covers transition/model drift while
  requiring contraction only of the reference rows A.  No exact fixed point is
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
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))
(defn- add-monotone [left left-prime right right-prime first second]
  (app (function/const* 'signed/add-monotone [])
       left left-prime right right-prime first second))
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- bridge-binders []
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)]
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['comparison-image vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['bridge-shape (same-shape right-image 'comparison-image)]
     ['comparison-residual-shape
      (same-shape 'comparison-image 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'gamma)]]))

(def bridged-approximate-threshold-certificate-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        bridge-distance (sup-distance right-image 'comparison-image)
        comparison-residual (sup-distance 'comparison-image 'right)
        right-residual (sup-distance right-image 'right)
        right-threshold-sum
        (sadd 'bridge-threshold 'comparison-residual-threshold)
        aggregate
        (sadd 'left-residual-threshold right-threshold-sum)
        binders
        (into
         (bridge-binders)
         [['left-residual-threshold signed]
          ['bridge-threshold signed]
          ['comparison-residual-threshold signed]
          ['left-residual-bound
           (sle left-residual 'left-residual-threshold)]
          ['bridge-bound (sle bridge-distance 'bridge-threshold)]
          ['comparison-residual-bound
           (sle comparison-residual 'comparison-residual-threshold)]])]
    {:name 'matrix/affine-nnrat-bridged-approximate-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      binders
      (let [right-residual-shape
            (shape-transitive
             right-image 'comparison-image 'right
             'bridge-shape 'comparison-residual-shape)
            triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             right-image 'comparison-image 'right
             'bridge-shape 'comparison-residual-shape)
            right-threshold-bound
            (add-monotone
             bridge-distance 'bridge-threshold
             comparison-residual 'comparison-residual-threshold
             'bridge-bound 'comparison-residual-bound)
            right-residual-bound
            (order-transitive
             right-residual
             (sadd bridge-distance comparison-residual)
             right-threshold-sum
             triangle right-threshold-bound)]
        (app
         (function/const*
          'matrix/affine-nnrat-two-threshold-stability-certificate [])
         'rows 'offset 'left 'right
         'gamma 'gamma-at-most-half
         'shape 'left-residual-shape right-residual-shape
         'offset-shape 'positive-rows 'bounded-sums
         'left-residual-threshold right-threshold-sum
         'left-residual-bound right-residual-bound)))}))

(def bridged-approximate-stability-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        bridge-distance (sup-distance right-image 'comparison-image)
        comparison-residual (sup-distance 'comparison-image 'right)
        aggregate
        (sadd left-residual (sadd bridge-distance comparison-residual))]
    {:name 'matrix/affine-nnrat-bridged-approximate-stability
     :universes []
     :type
     (function/forall
      (bridge-binders)
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      (bridge-binders)
      (app
       (function/const*
        'matrix/affine-nnrat-bridged-approximate-threshold-certificate [])
       'rows 'offset 'left 'right 'comparison-image
       'gamma 'gamma-at-most-half
       'shape 'left-residual-shape 'bridge-shape
       'comparison-residual-shape
       'offset-shape 'positive-rows 'bounded-sums
       left-residual bridge-distance comparison-residual
       (order-reflexive left-residual)
       (order-reflexive bridge-distance)
       (order-reflexive comparison-residual)))}))

(defn- operator-binders []
  (let [left-image
        (affine-action 'left-rows 'offset 'left)
        right-image
        (affine-action 'right-rows 'offset 'right)
        action-distance
        (sup-distance
         (action 'left-rows 'right)
         (action 'right-rows 'right))]
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['offset vector-type] ['left vector-type] ['right vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['left-offset-shape
      (same-shape 'offset (action 'left-rows 'left))]
     ['right-offset-shape
      (same-shape 'offset (action 'right-rows 'right))]
     ['positive-left-rows (rows-positive 'left-rows)]
     ['bounded-left-sums (row-sums-bounded 'left-rows 'gamma)]
     ['left-residual-threshold signed]
     ['operator-threshold signed]
     ['right-residual-threshold signed]
     ['left-residual-bound
      (sle (sup-distance 'left left-image)
           'left-residual-threshold)]
     ['operator-bound (sle action-distance 'operator-threshold)]
     ['right-residual-bound
      (sle (sup-distance right-image 'right)
           'right-residual-threshold)]]))

(def affine-row-perturbation-threshold-certificate-spec
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image-at-right
        (affine-action 'left-rows 'offset 'right)
        right-image-at-right
        (affine-action 'right-rows 'offset 'right)
        bridge-distance
        (sup-distance left-image-at-right right-image-at-right)
        action-distance
        (sup-distance left-action-at-right right-action-at-right)
        aggregate
        (sadd 'left-residual-threshold
              (sadd 'operator-threshold 'right-residual-threshold))]
    {:name 'matrix/affine-nnrat-row-perturbation-threshold-certificate
     :universes []
     :type
     (function/forall
      (operator-binders)
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      (operator-binders)
      (let [left-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'left-rows 'left 'right)
            left-offset-at-right-shape
            (shape-transitive
             'offset (action 'left-rows 'left) left-action-at-right
             'left-offset-shape left-action-shape)
            left-image-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'offset left-action-at-right left-offset-at-right-shape)
            right-image-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'offset right-action-at-right 'right-offset-shape)
            bridge-shape
            (shape-transitive
             left-image-at-right 'offset right-image-at-right
             left-image-offset-shape
             (shape-symmetric
              right-image-at-right 'offset right-image-offset-shape))
            bridge-action-same
            (app
             (function/const*
              'vector/sup-distance-add-left-same-shape [])
             'offset left-action-at-right right-action-at-right
             left-offset-at-right-shape 'right-offset-shape)
            bridge-bound
            (order-respects
             action-distance bridge-distance
             'operator-threshold 'operator-threshold
             (signed-symmetric
              bridge-distance action-distance bridge-action-same)
             (signed-reflexive 'operator-threshold)
             'operator-bound)]
        (app
         (function/const*
          'matrix/affine-nnrat-bridged-approximate-threshold-certificate [])
         'left-rows 'offset 'left 'right right-image-at-right
         'gamma 'gamma-at-most-half
         'shape 'left-residual-shape bridge-shape
         'right-residual-shape
         'left-offset-shape 'positive-left-rows 'bounded-left-sums
         'left-residual-threshold
         'operator-threshold 'right-residual-threshold
         'left-residual-bound bridge-bound 'right-residual-bound)))}))

(def definition-specs [])
(def theorem-specs
  [bridged-approximate-threshold-certificate-spec
   bridged-approximate-stability-spec
   affine-row-perturbation-threshold-certificate-spec])

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
  (-> env (extend-specs-if-missing :signed-vector-sup-translation translation/theorem-specs) (support/extend-with :finite-matrix-affine-operator-sensitivity theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-operator-sensitivity))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
