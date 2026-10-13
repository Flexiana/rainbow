(ns rainbow.math.linear.matrix.affine-general-rate-sensitivity
  "Sharp robustness certificates for arbitrary-rate affine problem drift.

  Let the reference rows A have canonical rational contraction rate
  `a/(a+g)`, where `a=ap+1` and `g=gp+1`.  This module specializes bridged
  inverse-gap stability to two independently checkable perturbation models:

    * operator drift, comparing `b+A*x` with `b+B*y`;
    * full drift, comparing `b+A*x` with `c+B*y`.

  The resulting factor is the sharp `(a+g)/g`, not the half-rate-only factor
  two.  The comparison rows B need not contract and neither candidate must be
  an exact fixed point.  Exact-distance and separate-threshold forms are
  theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-inverse-gap-stability
             :as stability]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-translation :as translation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
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
(defn- rate [ap gp]
  (make (succ ap) (nadd ap (succ gp))))
(defn- inverse [ap gp]
  (make (nadd (succ ap) (succ gp)) gp))
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

(defn- operator-binders []
  (let [left-image (affine-action 'left-rows 'offset 'left)
        right-image (affine-action 'right-rows 'offset 'right)]
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['offset vector-type] ['left vector-type] ['right vector-type]
     ['ap nat] ['gp nat]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['left-offset-shape
      (same-shape 'offset (action 'left-rows 'left))]
     ['right-offset-shape
      (same-shape 'offset (action 'right-rows 'right))]
     ['positive-left-rows (rows-positive 'left-rows)]
     ['bounded-left-sums
      (row-sums-bounded 'left-rows
                        (from-nnrat (rate 'ap 'gp)))]]))

(def affine-general-rate-row-perturbation-threshold-spec
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image (affine-action 'left-rows 'offset 'left)
        left-image-at-right
        (affine-action 'left-rows 'offset 'right)
        right-image-at-right
        (affine-action 'right-rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        bridge-distance
        (sup-distance left-image-at-right right-image-at-right)
        action-distance
        (sup-distance left-action-at-right right-action-at-right)
        right-residual (sup-distance right-image-at-right 'right)
        aggregate
        (sadd 'left-residual-threshold
              (sadd 'operator-threshold 'right-residual-threshold))
        binders
        (into
         (operator-binders)
         [['left-residual-threshold signed]
          ['operator-threshold signed]
          ['right-residual-threshold signed]
          ['left-residual-bound
           (sle left-residual 'left-residual-threshold)]
          ['operator-bound (sle action-distance 'operator-threshold)]
          ['right-residual-bound
           (sle right-residual 'right-residual-threshold)]])]
    {:name 'matrix/affine-general-rate-row-perturbation-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
     :value
     (function/lam
      binders
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
          'matrix/affine-general-rate-bridged-threshold-certificate [])
         'left-rows 'offset 'left 'right right-image-at-right
         'ap 'gp
         'shape 'left-residual-shape bridge-shape
         'right-residual-shape
         'left-offset-shape 'positive-left-rows 'bounded-left-sums
         'left-residual-threshold
         'operator-threshold 'right-residual-threshold
         'left-residual-bound bridge-bound 'right-residual-bound)))}))

(def affine-general-rate-row-perturbation-stability-spec
  (let [left-image (affine-action 'left-rows 'offset 'left)
        right-image (affine-action 'right-rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        action-distance
        (sup-distance
         (action 'left-rows 'right)
         (action 'right-rows 'right))
        right-residual (sup-distance right-image 'right)
        aggregate
        (sadd left-residual (sadd action-distance right-residual))]
    {:name 'matrix/affine-general-rate-row-perturbation-stability
     :universes []
     :type
     (function/forall
      (operator-binders)
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
     :value
     (function/lam
      (operator-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-row-perturbation-threshold-certificate [])
       'left-rows 'right-rows 'offset 'left 'right 'ap 'gp
       'shape 'left-residual-shape 'right-residual-shape
       'left-offset-shape 'right-offset-shape
       'positive-left-rows 'bounded-left-sums
       left-residual action-distance right-residual
       (order-reflexive left-residual)
       (order-reflexive action-distance)
       (order-reflexive right-residual)))}))

(defn- problem-binders []
  (let [left-action-at-right (action 'left-rows 'right)
        right-action-at-right (action 'right-rows 'right)
        left-image (affine-action 'left-rows 'left-offset 'left)
        right-image (affine-action 'right-rows 'right-offset 'right)]
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left vector-type] ['right vector-type]
     ['ap nat] ['gp nat]
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
     ['bounded-left-sums
      (row-sums-bounded 'left-rows
                        (from-nnrat (rate 'ap 'gp)))]]))

(def affine-general-rate-problem-perturbation-threshold-spec
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
    {:name 'matrix/affine-general-rate-problem-perturbation-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
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
          'matrix/affine-general-rate-bridged-threshold-certificate [])
         'left-rows 'left-offset 'left 'right comparison-image
         'ap 'gp
         'shape 'left-residual-shape bridge-shape
         'right-residual-shape
         'left-offset-shape 'positive-left-rows 'bounded-left-sums
         'left-residual-threshold offset-action-threshold
         'right-residual-threshold
         'left-residual-bound bridge-bound 'right-residual-bound)))}))

(def affine-general-rate-problem-perturbation-stability-spec
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
    {:name 'matrix/affine-general-rate-problem-perturbation-stability
     :universes []
     :type
     (function/forall
      (problem-binders)
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
     :value
     (function/lam
      (problem-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-problem-perturbation-threshold-certificate [])
       'left-rows 'right-rows 'left-offset 'right-offset 'left 'right
       'ap 'gp
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
  [affine-general-rate-row-perturbation-threshold-spec
   affine-general-rate-row-perturbation-stability-spec
   affine-general-rate-problem-perturbation-threshold-spec
   affine-general-rate-problem-perturbation-stability-spec])

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
  '[rainbow.math.linear.matrix.affine-inverse-gap-stability])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-specs-if-missing :signed-vector-sup-translation translation/theorem-specs) (support/extend-with :finite-matrix-affine-general-rate-sensitivity theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-general-rate-sensitivity))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
