(ns rainbow.math.linear.matrix.affine-residual-certificate
  "A posteriori error certificates for contractive signed affine systems.

  A half contraction and the triangle inequality give

      d(x,x*) <= d(x,Fx) + 1/2 d(x,x*).

  Additive order cancellation then moves the half-distance to the left, proving
  `d(x,x*) <= 2 d(x,Fx)`.  Thus a solver can certify its current error using the
  residual it can actually compute, without knowing the fixed point's value.
  The practical corollaries accept an NNRAT row bound gamma <= 1/2 and actual-row
  membership premises.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-strong-row-contraction
             :as strong]
            [rainbow.math.linear.matrix.equivalence-shape
             :as equivalence-shape]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-triangle :as scalar-triangle]
            [rainbow.math.rational.signed.vector-sup-triangle :as vector-triangle]
            [rainbow.math.linear.vector.equivalence-laws :as vector-laws]))

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
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
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
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(def signed-half-residual-bound-spec
  {:name 'signed/half-residual-bound :universes []
   :type
   (function/forall
    [['distance signed] ['residual signed]
     ['self-bound
      (sle 'distance
           (sadd 'residual (smul signed-half 'distance)))]]
    (sle 'distance (sadd 'residual 'residual)))
   :value
   (function/lam
    [['distance signed] ['residual signed]
     ['self-bound
      (sle 'distance
           (sadd 'residual (smul signed-half 'distance)))]]
    (let [half-distance (smul signed-half 'distance)
          split (sadd half-distance half-distance)
          padded (sadd 'residual half-distance)
          split-same-distance
          (app (function/const* 'signed/half-scale-add-self [])
               'distance)
          split-bound
          (order-respects
           'distance split padded padded
           (signed-symmetric split 'distance split-same-distance)
           (signed-reflexive padded)
           'self-bound)
          half-at-most-residual
          (app (function/const* 'signed/at-most-add-right-cancel [])
               half-distance 'residual half-distance split-bound)
          doubled-half-bound
          (add-monotone
           half-distance 'residual half-distance 'residual
           half-at-most-residual half-at-most-residual)]
      (order-respects
       split 'distance
       (sadd 'residual 'residual) (sadd 'residual 'residual)
       split-same-distance
       (signed-reflexive (sadd 'residual 'residual))
       doubled-half-bound)))})

(defn- half-row-binders []
  [['rows matrix-type] ['offset vector-type]
   ['approximate vector-type] ['fixed-point vector-type]
   ['shape (same-shape 'approximate 'fixed-point)]
   ['offset-shape
    (same-shape 'offset (action 'rows 'approximate))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (row-sums-bounded 'rows signed-half)]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]])

(def affine-half-row-fixed-point-residual-bound-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        fixed-image (affine-action 'rows 'offset 'fixed-point)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)
        image-pair-distance (sup-distance image fixed-image)
        image-fixed-distance (sup-distance image 'fixed-point)
        half-distance (smul signed-half distance)]
    {:name 'matrix/affine-half-row-fixed-point-residual-bound
     :universes []
     :type
     (function/forall
      (half-row-binders)
      (sle distance (sadd residual residual)))
     :value
     (function/lam
      (half-row-binders)
      (let [image-pair-shape
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'offset 'approximate 'fixed-point 'offset-shape)
            fixed-image-shape
            (app
             (function/const* 'vector/equivalent-implies-same-shape [])
             fixed-image 'fixed-point 'fixed)
            image-fixed-shape
            (shape-transitive
             image fixed-image 'fixed-point
             image-pair-shape fixed-image-shape)
            approximate-image-shape
            (shape-transitive
             'approximate 'fixed-point image
             'shape
             (shape-symmetric image 'fixed-point image-fixed-shape))
            triangle-bound
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             'approximate image 'fixed-point
             approximate-image-shape image-fixed-shape)
            image-pair-bound
            (app
             (function/const*
              'matrix/affine-action-row-sum-lipschitz [])
             'rows 'offset 'approximate 'fixed-point signed-half
             (function/const* 'signed/zero-at-most-half [])
             'shape 'offset-shape 'positive-rows 'bounded-sums)
            image-distance-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             image fixed-image 'fixed-point 'fixed)
            image-fixed-bound
            (order-respects
             image-pair-distance image-fixed-distance
             half-distance half-distance
             image-distance-same (signed-reflexive half-distance)
             image-pair-bound)
            sum-bound
            (add-monotone
             residual residual image-fixed-distance half-distance
             (order-reflexive residual) image-fixed-bound)
            self-bound
            (order-transitive
             distance (sadd residual image-fixed-distance)
             (sadd residual half-distance)
             triangle-bound sum-bound)]
        (app (function/const* 'signed/half-residual-bound [])
             distance residual self-bound)))}))

(defn- strong-row-binders []
  [['rows matrix-type] ['offset vector-type]
   ['approximate vector-type] ['fixed-point vector-type]
   ['gamma nnrat]
   ['gamma-at-most-half (rle 'gamma nnrat-half)]
   ['shape (same-shape 'approximate 'fixed-point)]
   ['offset-shape
    (same-shape 'offset (action 'rows 'approximate))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat 'gamma))]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]])

(def affine-strong-row-fixed-point-residual-bound-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)]
    {:name 'matrix/affine-nnrat-strong-row-fixed-point-residual-bound
     :universes []
     :type
     (function/forall
      (strong-row-binders)
      (sle distance (sadd residual residual)))
     :value
     (function/lam
      (strong-row-binders)
      (app
       (function/const*
        'matrix/affine-half-row-fixed-point-residual-bound [])
       'rows 'offset 'approximate 'fixed-point
       'shape 'offset-shape 'positive-rows
       (app
        (function/const* 'matrix/nnrat-row-sums-imply-half-bound [])
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'fixed))}))

(def affine-strong-row-stopping-certificate-spec
  (let [binders
        (conj
         (strong-row-binders)
         ['threshold signed]
         ['residual-at-most-threshold
          (sle
           (sup-distance
            'approximate
            (affine-action 'rows 'offset 'approximate))
           'threshold)])
        distance (sup-distance 'approximate 'fixed-point)
        residual
        (sup-distance
         'approximate (affine-action 'rows 'offset 'approximate))]
    {:name 'matrix/affine-nnrat-strong-row-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle distance (sadd 'threshold 'threshold)))
     :value
     (function/lam
      binders
      (let [residual-bound
            (app
             (function/const*
              'matrix/affine-nnrat-strong-row-fixed-point-residual-bound [])
             'rows 'offset 'approximate 'fixed-point
             'gamma 'gamma-at-most-half
             'shape 'offset-shape 'positive-rows 'bounded-sums 'fixed)
            doubled-threshold-bound
            (add-monotone
             residual 'threshold residual 'threshold
             'residual-at-most-threshold
             'residual-at-most-threshold)]
        (order-transitive
         distance (sadd residual residual)
         (sadd 'threshold 'threshold)
         residual-bound doubled-threshold-bound)))}))

(def definition-specs [])
(def theorem-specs
  [signed-half-residual-bound-spec
   affine-half-row-fixed-point-residual-bound-spec
   affine-strong-row-fixed-point-residual-bound-spec
   affine-strong-row-stopping-certificate-spec])

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
      strong/extend-environment
      (extend-specs-if-missing
       :signed-distance-triangle scalar-triangle/theorem-specs)
      (extend-spec-if-missing
       'vector/sup-distance-triangle-same-shape
       :signed-vector-sup-triangle
       vector-triangle/sup-distance-triangle-same-shape-spec)
      (extend-spec-if-missing
       'vector/map-respects-equivalence
       :vector-equivalence-laws
       vector-laws/map-respects-equivalence-spec)
      (extend-spec-if-missing
       'vector/equivalent-implies-same-shape
       :finite-matrix-equivalence-shape
       equivalence-shape/vector-equivalent-implies-same-shape-spec)
      (support/extend-with
       :finite-matrix-affine-residual-certificate theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
