(ns rainbow.math.linear.matrix.affine-problem-sensitivity
  "End-to-end robustness for approximate affine optimization problems.

  Compare x certified for `b + A*x` with y certified for `c + B*y`.  If A is
  contractive, the total disagreement is bounded by twice the sum of four
  independently checkable quantities: x's residual, offset/reward drift,
  operator/transition drift at y, and y's residual.

      d(x,y) <= 2 * (r_x + ((d(b,c) + d(A*y,B*y)) + r_y)).

  No contraction premise is imposed on B and no exact fixed point is assumed.
  The exact-distance theorem and separate four-threshold certificate are
  theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-operator-sensitivity
             :as operator]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

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

(defn- problem-binders []
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image (affine-action 'left-rows 'left-offset 'left)
        right-image (affine-action 'right-rows 'right-offset 'right)]
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left vector-type] ['right vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['left-offset-shape
      (same-shape 'left-offset (action 'left-rows 'left))]
     ['right-offset-shape
      (same-shape 'right-offset right-action-at-right)]
     ['action-bridge-shape
      (same-shape left-action-at-right right-action-at-right)]
     ['positive-left-rows (rows-positive 'left-rows)]
     ['bounded-left-sums (row-sums-bounded 'left-rows 'gamma)]]))

(def problem-perturbation-threshold-certificate-spec
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image (affine-action 'left-rows 'left-offset 'left)
        reference-image
        (affine-action 'left-rows 'left-offset 'right)
        offset-shift-image
        (affine-action 'left-rows 'right-offset 'right)
        comparison-image
        (affine-action 'right-rows 'right-offset 'right)
        left-residual (sup-distance 'left left-image)
        offset-distance (sup-distance 'left-offset 'right-offset)
        action-distance
        (sup-distance left-action-at-right right-action-at-right)
        right-residual (sup-distance comparison-image 'right)
        offset-action-threshold
        (sadd 'offset-threshold 'operator-threshold)
        aggregate
        (sadd 'left-residual-threshold
              (sadd offset-action-threshold
                    'right-residual-threshold))
        binders
        (into
         (problem-binders)
         [['left-residual-threshold signed]
          ['offset-threshold signed]
          ['operator-threshold signed]
          ['right-residual-threshold signed]
          ['left-residual-bound
           (sle left-residual 'left-residual-threshold)]
          ['offset-bound (sle offset-distance 'offset-threshold)]
          ['operator-bound (sle action-distance 'operator-threshold)]
          ['right-residual-bound
           (sle right-residual 'right-residual-threshold)]])]
    {:name 'matrix/affine-nnrat-problem-perturbation-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      binders
      (let [left-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'left-rows 'left 'right)
            left-offset-at-right-shape
            (shape-transitive
             'left-offset (action 'left-rows 'left) left-action-at-right
             'left-offset-shape left-action-shape)
            right-offset-at-left-action-shape
            (shape-transitive
             'right-offset right-action-at-right left-action-at-right
             'right-offset-shape
             (shape-symmetric
              left-action-at-right right-action-at-right
              'action-bridge-shape))
            offset-shape
            (shape-transitive
             'left-offset left-action-at-right 'right-offset
             left-offset-at-right-shape
             (shape-symmetric
              'right-offset left-action-at-right
              right-offset-at-left-action-shape))
            reference-left-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'left-offset left-action-at-right
             left-offset-at-right-shape)
            shifted-right-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'right-offset left-action-at-right
             right-offset-at-left-action-shape)
            comparison-right-offset-shape
            (app
             (function/const* 'vector/add-preserves-left-shape [])
             'right-offset right-action-at-right 'right-offset-shape)
            reference-shift-shape
            (shape-transitive
             reference-image 'left-offset offset-shift-image
             reference-left-offset-shape
             (shape-transitive
              'left-offset 'right-offset offset-shift-image
              offset-shape
              (shape-symmetric
               offset-shift-image 'right-offset
               shifted-right-offset-shape)))
            shift-comparison-shape
            (shape-transitive
             offset-shift-image 'right-offset comparison-image
             shifted-right-offset-shape
             (shape-symmetric
              comparison-image 'right-offset
              comparison-right-offset-shape))
            bridge-shape
            (shape-transitive
             reference-image offset-shift-image comparison-image
             reference-shift-shape shift-comparison-shape)
            bridge-triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             reference-image offset-shift-image comparison-image
             reference-shift-shape shift-comparison-shape)
            offset-translation
            (app
             (function/const*
              'vector/sup-distance-add-right-same-shape [])
             'left-offset 'right-offset left-action-at-right
             (shape-symmetric
              'left-offset left-action-at-right
              left-offset-at-right-shape)
             (shape-symmetric
              'right-offset left-action-at-right
              right-offset-at-left-action-shape))
            shifted-offset-distance
            (sup-distance reference-image offset-shift-image)
            shifted-offset-bound
            (order-respects
             offset-distance shifted-offset-distance
             'offset-threshold 'offset-threshold
             (signed-symmetric
              shifted-offset-distance offset-distance offset-translation)
             (signed-reflexive 'offset-threshold)
             'offset-bound)
            operator-translation
            (app
             (function/const*
              'vector/sup-distance-add-left-same-shape [])
             'right-offset left-action-at-right right-action-at-right
             right-offset-at-left-action-shape 'right-offset-shape)
            shifted-operator-distance
            (sup-distance offset-shift-image comparison-image)
            shifted-operator-bound
            (order-respects
             action-distance shifted-operator-distance
             'operator-threshold 'operator-threshold
             (signed-symmetric
              shifted-operator-distance action-distance
              operator-translation)
             (signed-reflexive 'operator-threshold)
             'operator-bound)
            bridge-sum-bound
            (add-monotone
             shifted-offset-distance 'offset-threshold
             shifted-operator-distance 'operator-threshold
             shifted-offset-bound shifted-operator-bound)
            bridge-bound
            (order-transitive
             (sup-distance reference-image comparison-image)
             (sadd shifted-offset-distance shifted-operator-distance)
             offset-action-threshold
             bridge-triangle bridge-sum-bound)]
        (app
         (function/const*
          'matrix/affine-nnrat-bridged-approximate-threshold-certificate [])
         'left-rows 'left-offset 'left 'right comparison-image
         'gamma 'gamma-at-most-half
         'shape 'left-residual-shape bridge-shape
         'right-residual-shape
         'left-offset-shape 'positive-left-rows 'bounded-left-sums
         'left-residual-threshold offset-action-threshold
         'right-residual-threshold
         'left-residual-bound bridge-bound 'right-residual-bound)))}))

(def problem-perturbation-stability-spec
  (let [left-image (affine-action 'left-rows 'left-offset 'left)
        right-image (affine-action 'right-rows 'right-offset 'right)
        left-residual (sup-distance 'left left-image)
        offset-distance (sup-distance 'left-offset 'right-offset)
        action-distance
        (sup-distance
         (action 'left-rows 'right)
         (action 'right-rows 'right))
        right-residual (sup-distance right-image 'right)
        aggregate
        (sadd left-residual
              (sadd (sadd offset-distance action-distance)
                    right-residual))]
    {:name 'matrix/affine-nnrat-problem-perturbation-stability
     :universes []
     :type
     (function/forall
      (problem-binders)
      (sle (sup-distance 'left 'right) (sadd aggregate aggregate)))
     :value
     (function/lam
      (problem-binders)
      (app
       (function/const*
        'matrix/affine-nnrat-problem-perturbation-threshold-certificate [])
       'left-rows 'right-rows 'left-offset 'right-offset 'left 'right
       'gamma 'gamma-at-most-half
       'shape 'left-residual-shape 'right-residual-shape
       'left-offset-shape 'right-offset-shape 'action-bridge-shape
       'positive-left-rows 'bounded-left-sums
       left-residual offset-distance action-distance right-residual
       (order-reflexive left-residual)
       (order-reflexive offset-distance)
       (order-reflexive action-distance)
       (order-reflexive right-residual)))}))

(def definition-specs [])
(def theorem-specs
  [problem-perturbation-threshold-certificate-spec
   problem-perturbation-stability-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-operator-sensitivity])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-problem-sensitivity theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-problem-sensitivity))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
