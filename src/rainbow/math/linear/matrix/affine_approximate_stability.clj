(ns rainbow.math.linear.matrix.affine-approximate-stability
  "A posteriori stability of approximate affine fixed points.

  For a half-contractive affine map F, two arbitrary candidates x and y obey

      d(x,y) <= 2 * (d(x,Fx) + d(y,Fy)).

  Unlike fixed-point uniqueness, this theorem needs no exact fixed point and is
  directly usable by independently implemented solvers: their computable
  residual certificates bound their disagreement.  The practical theorem
  accepts an NNRAT row bound gamma <= 1/2 and separate residual thresholds.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-residual-certificate
             :as residual]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.add-associative :as associative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
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
(defn- seq-equiv [left right]
  (app (function/const* 'signed/equivalent []) left right))
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
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
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
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- half-row-binders []
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)]
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows signed-half)]]))

(def affine-half-row-approximate-fixed-points-stable-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        distance (sup-distance 'left 'right)
        left-residual (sup-distance 'left left-image)
        image-distance (sup-distance left-image right-image)
        right-residual (sup-distance right-image 'right)
        left-image-to-right (sup-distance left-image 'right)
        residual-sum (sadd left-residual right-residual)
        half-distance (smul signed-half distance)
        three-segment (sadd left-residual
                            (sadd image-distance right-residual))
        reordered (sadd residual-sum image-distance)]
    {:name 'matrix/affine-half-row-approximate-fixed-points-stable
     :universes []
     :type
     (function/forall
      (half-row-binders)
      (sle distance (sadd residual-sum residual-sum)))
     :value
     (function/lam
      (half-row-binders)
      (let [image-shape
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'offset 'left 'right 'offset-shape)
            left-image-right-shape
            (shape-transitive
             left-image right-image 'right
             image-shape 'right-residual-shape)
            outer-triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             'left left-image 'right
             'left-residual-shape left-image-right-shape)
            inner-triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             left-image right-image 'right
             image-shape 'right-residual-shape)
            expand-second-leg
            (add-monotone
             left-residual left-residual
             left-image-to-right (sadd image-distance right-residual)
             (order-reflexive left-residual) inner-triangle)
            three-segment-bound
            (order-transitive
             distance (sadd left-residual left-image-to-right)
             three-segment outer-triangle expand-second-leg)
            swap-inner
            (app (function/const* 'signed/add-commutative [])
                 image-distance right-residual)
            lift-swap
            (app (function/const* 'signed/add-respects-equivalence [])
                 left-residual left-residual
                 (sadd image-distance right-residual)
                 (sadd right-residual image-distance)
                 (signed-reflexive left-residual) swap-inner)
            reassociate
            (app (function/const* 'signed/add-associative [])
                 left-residual right-residual image-distance)
            three-to-reordered
            (signed-transitive
             three-segment
             (sadd left-residual (sadd right-residual image-distance))
             reordered
             lift-swap
             (signed-symmetric
              reordered
              (sadd left-residual (sadd right-residual image-distance))
              reassociate))
            reordered-bound
            (order-respects
             distance distance three-segment reordered
             (signed-reflexive distance) three-to-reordered
             three-segment-bound)
            contraction
            (app
             (function/const*
              'matrix/affine-action-row-sum-lipschitz [])
             'rows 'offset 'left 'right signed-half
             (function/const* 'signed/zero-at-most-half [])
             'shape 'offset-shape 'positive-rows 'bounded-sums)
            contract-middle
            (add-monotone
             residual-sum residual-sum image-distance half-distance
             (order-reflexive residual-sum) contraction)
            self-bound
            (order-transitive
             distance reordered (sadd residual-sum half-distance)
             reordered-bound contract-middle)]
        (app (function/const* 'signed/half-residual-bound [])
             distance residual-sum self-bound)))}))

(defn- strong-row-binders []
  (let [base (vec (butlast (half-row-binders)))]
    (into
     (subvec base 0 4)
     (concat
      [['gamma nnrat]
       ['gamma-at-most-half (rle 'gamma nnrat-half)]]
      (subvec base 4 9)
      [['bounded-sums
        (row-sums-bounded 'rows (from-nnrat 'gamma))]]))))

(def affine-strong-row-approximate-fixed-points-stable-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        residual-sum
        (sadd (sup-distance 'left left-image)
              (sup-distance right-image 'right))]
    {:name 'matrix/affine-nnrat-approximate-fixed-points-stable
     :universes []
     :type
     (function/forall
      (strong-row-binders)
      (sle (sup-distance 'left 'right)
           (sadd residual-sum residual-sum)))
     :value
     (function/lam
      (strong-row-binders)
      (app
       (function/const*
        'matrix/affine-half-row-approximate-fixed-points-stable [])
       'rows 'offset 'left 'right
       'shape 'left-residual-shape 'right-residual-shape
       'offset-shape 'positive-rows
       (app
        (function/const* 'matrix/nnrat-row-sums-imply-half-bound [])
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)))}))

(def affine-strong-row-two-threshold-stability-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        right-residual (sup-distance right-image 'right)
        residual-sum (sadd left-residual right-residual)
        threshold-sum (sadd 'left-threshold 'right-threshold)
        binders
        (into
         (strong-row-binders)
         [['left-threshold signed] ['right-threshold signed]
          ['left-residual-bound (sle left-residual 'left-threshold)]
          ['right-residual-bound (sle right-residual 'right-threshold)]])]
    {:name 'matrix/affine-nnrat-two-threshold-stability-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (sadd threshold-sum threshold-sum)))
     :value
     (function/lam
      binders
      (let [residual-stability
            (app
             (function/const*
              'matrix/affine-nnrat-approximate-fixed-points-stable [])
             'rows 'offset 'left 'right
             'gamma 'gamma-at-most-half
             'shape 'left-residual-shape 'right-residual-shape
             'offset-shape 'positive-rows 'bounded-sums)
            threshold-bound
            (add-monotone
             left-residual 'left-threshold
             right-residual 'right-threshold
             'left-residual-bound 'right-residual-bound)
            doubled-threshold-bound
            (add-monotone
             residual-sum threshold-sum residual-sum threshold-sum
             threshold-bound threshold-bound)]
        (order-transitive
         (sup-distance 'left 'right)
         (sadd residual-sum residual-sum)
         (sadd threshold-sum threshold-sum)
         residual-stability doubled-threshold-bound)))}))

(def definition-specs [])
(def theorem-specs
  [affine-half-row-approximate-fixed-points-stable-spec
   affine-strong-row-approximate-fixed-points-stable-spec
   affine-strong-row-two-threshold-stability-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      residual/extend-environment
      (extend-spec-if-missing
       'signed/add-associative
       :signed-add-associative
       associative/add-associative-spec)
      (support/extend-with
       :finite-matrix-affine-approximate-stability theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
