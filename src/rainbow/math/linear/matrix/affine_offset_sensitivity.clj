(ns rainbow.math.linear.matrix.affine-offset-sensitivity
  "Sensitivity of contractive affine fixed points to offset perturbations.

  If the same nonnegative matrix has row sums at most one half, fixed points of
  `b + A*x` and `c + A*y` satisfy

      d(x,y) <= 2 * d(b,c).

  The proof combines contraction in the value argument with exact translation
  invariance in the offset argument, then applies additive half cancellation.
  A practical NNRAT gamma <= 1/2 wrapper and a threshold certificate expose the
  result to solver/reward perturbation analyses.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-residual-certificate
             :as residual]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-translation :as translation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-half
  (function/app (function/const* 'signed/from-nnrat []) nnrat-half))
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
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
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
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))
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
(defn- vector-symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- half-row-binders []
  (let [left-action (action 'rows 'left)
        right-action (action 'rows 'right)]
    [['rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['left-offset-shape (same-shape 'left-offset left-action)]
     ['right-offset-shape (same-shape 'right-offset right-action)]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows signed-half)]
     ['left-fixed
      (vector-equivalent
       (affine-action 'rows 'left-offset 'left) 'left)]
     ['right-fixed
      (vector-equivalent
       (affine-action 'rows 'right-offset 'right) 'right)]]))

(def affine-half-row-offset-fixed-point-sensitivity-spec
  (let [left-action (action 'rows 'left)
        right-action (action 'rows 'right)
        left-image (affine-action 'rows 'left-offset 'left)
        common-offset-image (affine-action 'rows 'left-offset 'right)
        right-image (affine-action 'rows 'right-offset 'right)
        distance (sup-distance 'left 'right)
        image-distance (sup-distance left-image right-image)
        contracted-distance (sup-distance left-image common-offset-image)
        offset-image-distance
        (sup-distance common-offset-image right-image)
        offset-distance (sup-distance 'left-offset 'right-offset)
        half-distance (smul signed-half distance)]
    {:name 'matrix/affine-half-row-offset-fixed-point-sensitivity
     :universes []
     :type
     (function/forall
      (half-row-binders)
      (sle distance (sadd offset-distance offset-distance)))
     :value
     (function/lam
      (half-row-binders)
      (let [right-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'rows 'left 'right)
            left-offset-right-shape
            (shape-transitive
             'left-offset left-action right-action
             'left-offset-shape right-action-shape)
            offset-shape
            (shape-transitive
             'left-offset right-action 'right-offset
             left-offset-right-shape
             (shape-symmetric
              'right-offset right-action 'right-offset-shape))
            common-image-left-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'left-offset right-action left-offset-right-shape)
            right-image-right-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'right-offset right-action 'right-offset-shape)
            common-right-image-shape
            (shape-transitive
             common-offset-image 'left-offset right-image
             common-image-left-offset-shape
             (shape-transitive
              'left-offset 'right-offset right-image
              offset-shape
              (shape-symmetric
               right-image 'right-offset
               right-image-right-offset-shape)))
            left-common-shape
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'left-offset 'left 'right 'left-offset-shape)
            triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             left-image common-offset-image right-image
             left-common-shape common-right-image-shape)
            contraction
            (app
             (function/const*
              'matrix/affine-action-row-sum-lipschitz [])
             'rows 'left-offset 'left 'right signed-half
             (function/const* 'signed/zero-at-most-half [])
             'shape 'left-offset-shape 'positive-rows 'bounded-sums)
            offset-translation
            (app
             (function/const*
              'vector/sup-distance-add-right-same-shape [])
             'left-offset 'right-offset right-action
             (shape-symmetric
              'left-offset right-action left-offset-right-shape)
             (shape-symmetric
              'right-offset right-action 'right-offset-shape))
            offset-bound
            (app (function/const* 'signed/equivalent-to-at-most [])
                 offset-image-distance offset-distance
                 offset-translation)
            image-sum-bound
            (add-monotone
             contracted-distance half-distance
             offset-image-distance offset-distance
             contraction offset-bound)
            image-bound
            (order-transitive
             image-distance
             (sadd contracted-distance offset-image-distance)
             (sadd half-distance offset-distance)
             triangle image-sum-bound)
            fixed-distance-same
            (app
             (function/const*
              'vector/sup-distance-respects-equivalence [])
             'left left-image 'right right-image
             (vector-symmetric left-image 'left 'left-fixed)
             (vector-symmetric right-image 'right 'right-fixed))
            distance-bound-unordered
            (order-respects
             image-distance distance
             (sadd half-distance offset-distance)
             (sadd half-distance offset-distance)
             (signed-symmetric distance image-distance fixed-distance-same)
             (signed-reflexive (sadd half-distance offset-distance))
             image-bound)
            commute-sum
            (app (function/const* 'signed/add-commutative [])
                 half-distance offset-distance)
            self-bound
            (order-respects
             distance distance
             (sadd half-distance offset-distance)
             (sadd offset-distance half-distance)
             (signed-reflexive distance) commute-sum
             distance-bound-unordered)]
        (app (function/const* 'signed/half-residual-bound [])
             distance offset-distance self-bound)))}))

(defn- strong-row-binders []
  (let [half (half-row-binders)]
    (into
     (subvec (vec half) 0 5)
     (concat
      [['gamma nnrat]
       ['gamma-at-most-half (rle 'gamma nnrat-half)]]
      (subvec (vec half) 5 9)
      [['bounded-sums
        (row-sums-bounded 'rows (from-nnrat 'gamma))]]
      (subvec (vec half) 10)))))

(def affine-strong-row-offset-fixed-point-sensitivity-spec
  (let [distance (sup-distance 'left 'right)
        offset-distance (sup-distance 'left-offset 'right-offset)]
    {:name 'matrix/affine-nnrat-offset-fixed-point-sensitivity
     :universes []
     :type
     (function/forall
      (strong-row-binders)
      (sle distance (sadd offset-distance offset-distance)))
     :value
     (function/lam
      (strong-row-binders)
      (app
       (function/const*
        'matrix/affine-half-row-offset-fixed-point-sensitivity [])
       'rows 'left-offset 'right-offset 'left 'right
       'shape 'left-offset-shape 'right-offset-shape
       'positive-rows
       (app
        (function/const* 'matrix/nnrat-row-sums-imply-half-bound [])
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'left-fixed 'right-fixed))}))

(def affine-strong-row-offset-threshold-sensitivity-spec
  (let [distance (sup-distance 'left 'right)
        offset-distance (sup-distance 'left-offset 'right-offset)
        binders
        (into
         (strong-row-binders)
         [['threshold signed]
          ['offset-distance-bound (sle offset-distance 'threshold)]])]
    {:name 'matrix/affine-nnrat-offset-threshold-sensitivity-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle distance (sadd 'threshold 'threshold)))
     :value
     (function/lam
      binders
      (let [sensitivity
            (app
             (function/const*
              'matrix/affine-nnrat-offset-fixed-point-sensitivity [])
             'rows 'left-offset 'right-offset 'left 'right
             'gamma 'gamma-at-most-half
             'shape 'left-offset-shape 'right-offset-shape
             'positive-rows 'bounded-sums 'left-fixed 'right-fixed)
            threshold-double
            (add-monotone
             offset-distance 'threshold offset-distance 'threshold
             'offset-distance-bound 'offset-distance-bound)]
        (order-transitive
         distance (sadd offset-distance offset-distance)
         (sadd 'threshold 'threshold)
         sensitivity threshold-double)))}))

(def definition-specs [])
(def theorem-specs
  [affine-half-row-offset-fixed-point-sensitivity-spec
   affine-strong-row-offset-fixed-point-sensitivity-spec
   affine-strong-row-offset-threshold-sensitivity-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(defn extend-environment [env]
  (-> env
      residual/extend-environment
      (extend-specs-if-missing
       :signed-vector-sup-translation translation/theorem-specs)
      (support/extend-with
       :finite-matrix-affine-offset-sensitivity theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
