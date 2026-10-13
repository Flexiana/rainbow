(ns rainbow.math.linear.matrix.affine-inverse-gap-certificate
  "Sharp residual certificates for arbitrary strict contraction rates.

  The scalar theorem abstracts the exact algebra needed beyond the special
  half-rate case.  If `rate + gap ~ 1`, `inverse * gap ~ 1`, inverse is
  nonnegative, and

      distance <= residual + rate*distance,

  then `distance <= inverse*residual`.  Affine matrix theorems derive that
  self-bound from row-sum Lipschitz contraction and expose a stopping
  certificate.  Instantiating inverse with `(1-rate)^-1` gives the sharp
  a-posteriori factor for any rational rate below one.  Theorem-only,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual-certificate
             :as residual]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- seq-equiv [left right]
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
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- inverse-gap-binders [distance residual]
  [['rate signed] ['gap signed] ['inverse signed]
   ['inverse-nonnegative (sle signed-zero 'inverse)]
   ['rate-plus-gap-one
    (seq-equiv (sadd 'rate 'gap) signed-one)]
   ['inverse-times-gap-one
    (seq-equiv (smul 'inverse 'gap) signed-one)]
   ['self-bound
    (sle distance (sadd residual (smul 'rate distance)))]] )

(def inverse-gap-residual-bound-spec
  {:name 'signed/inverse-gap-residual-bound :universes []
   :type
   (function/forall
    (into
     [['distance signed] ['residual signed]]
     (inverse-gap-binders 'distance 'residual))
    (sle 'distance (smul 'inverse 'residual)))
   :value
   (function/lam
    (into
     [['distance signed] ['residual signed]]
     (inverse-gap-binders 'distance 'residual))
    (let [gap-distance (smul 'gap 'distance)
          rate-distance (smul 'rate 'distance)
          split (sadd gap-distance rate-distance)
          combined (smul (sadd 'gap 'rate) 'distance)
          one-distance (smul signed-one 'distance)
          padded (sadd 'residual rate-distance)
          gap-plus-rate-one
          (signed-transitive
           (sadd 'gap 'rate) (sadd 'rate 'gap) signed-one
           (app (function/const* 'signed/add-commutative [])
                'gap 'rate)
           'rate-plus-gap-one)
          combined-distance
          (signed-transitive
           combined one-distance 'distance
           (app
            (function/const*
             'signed/multiply-right-respects-equivalence [])
            (sadd 'gap 'rate) signed-one 'distance
            gap-plus-rate-one)
           (app (function/const* 'signed/multiply-one-left [])
                'distance))
          split-distance
          (signed-transitive
           split combined 'distance
           (signed-symmetric
            combined split
            (app
             (function/const*
              'signed/multiply-distributes-add-right [])
             'gap 'rate 'distance))
           combined-distance)
          split-bound
          (order-respects
           'distance split padded padded
           (signed-symmetric split 'distance split-distance)
           (signed-reflexive padded)
           'self-bound)
          gap-at-most-residual
          (app (function/const* 'signed/at-most-add-right-cancel [])
               gap-distance 'residual rate-distance split-bound)
          scaled-gap (smul 'inverse gap-distance)
          scaled-residual (smul 'inverse 'residual)
          scaled-bound
          (app (function/const* 'signed/multiply-left-monotone [])
               'inverse gap-distance 'residual
               'inverse-nonnegative gap-at-most-residual)
          regrouped (smul (smul 'inverse 'gap) 'distance)
          scaled-gap-distance
          (signed-transitive
           scaled-gap regrouped 'distance
           (signed-symmetric
            regrouped scaled-gap
            (app (function/const* 'signed/multiply-associative [])
                 'inverse 'gap 'distance))
           (signed-transitive
            regrouped one-distance 'distance
            (app
             (function/const*
              'signed/multiply-right-respects-equivalence [])
             (smul 'inverse 'gap) signed-one 'distance
             'inverse-times-gap-one)
            (app (function/const* 'signed/multiply-one-left [])
                 'distance)))]
      (order-respects
       scaled-gap 'distance scaled-residual scaled-residual
       scaled-gap-distance (signed-reflexive scaled-residual)
       scaled-bound)))})

(defn- affine-binders []
  [['rows matrix-type] ['offset vector-type]
   ['approximate vector-type] ['fixed-point vector-type]
   ['rate signed] ['gap signed] ['inverse signed]
   ['rate-nonnegative (sle signed-zero 'rate)]
   ['inverse-nonnegative (sle signed-zero 'inverse)]
   ['rate-plus-gap-one
    (seq-equiv (sadd 'rate 'gap) signed-one)]
   ['inverse-times-gap-one
    (seq-equiv (smul 'inverse 'gap) signed-one)]
   ['shape (same-shape 'approximate 'fixed-point)]
   ['offset-shape
    (same-shape 'offset (action 'rows 'approximate))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (row-sums-bounded 'rows 'rate)]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]])

(def affine-inverse-gap-fixed-point-residual-bound-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        fixed-image (affine-action 'rows 'offset 'fixed-point)
        distance (sup-distance 'approximate 'fixed-point)
        residual-distance (sup-distance 'approximate image)
        image-pair-distance (sup-distance image fixed-image)
        image-fixed-distance (sup-distance image 'fixed-point)
        scaled-distance (smul 'rate distance)]
    {:name 'matrix/affine-inverse-gap-fixed-point-residual-bound
     :universes []
     :type
     (function/forall
      (affine-binders)
      (sle distance (smul 'inverse residual-distance)))
     :value
     (function/lam
      (affine-binders)
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
            triangle
            (app
             (function/const*
              'vector/sup-distance-triangle-same-shape [])
             'approximate image 'fixed-point
             approximate-image-shape image-fixed-shape)
            image-pair-bound
            (app
             (function/const*
              'matrix/affine-action-row-sum-lipschitz [])
             'rows 'offset 'approximate 'fixed-point 'rate
             'rate-nonnegative 'shape 'offset-shape
             'positive-rows 'bounded-sums)
            image-distance-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             image fixed-image 'fixed-point 'fixed)
            image-fixed-bound
            (order-respects
             image-pair-distance image-fixed-distance
             scaled-distance scaled-distance
             image-distance-same (signed-reflexive scaled-distance)
             image-pair-bound)
            sum-bound
            (add-monotone
             residual-distance residual-distance
             image-fixed-distance scaled-distance
             (order-reflexive residual-distance) image-fixed-bound)
            self-bound
            (order-transitive
             distance (sadd residual-distance image-fixed-distance)
             (sadd residual-distance scaled-distance)
             triangle sum-bound)]
        (app
         (function/const* 'signed/inverse-gap-residual-bound [])
         distance residual-distance 'rate 'gap 'inverse
         'inverse-nonnegative
         'rate-plus-gap-one 'inverse-times-gap-one self-bound)))}))

(def affine-inverse-gap-stopping-certificate-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual-distance (sup-distance 'approximate image)
        binders
        (into
         (affine-binders)
         [['threshold signed]
          ['residual-at-most-threshold
           (sle residual-distance 'threshold)]])]
    {:name 'matrix/affine-inverse-gap-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle distance (smul 'inverse 'threshold)))
     :value
     (function/lam
      binders
      (let [residual-bound
            (app
             (function/const*
              'matrix/affine-inverse-gap-fixed-point-residual-bound [])
             'rows 'offset 'approximate 'fixed-point
             'rate 'gap 'inverse
             'rate-nonnegative 'inverse-nonnegative
             'rate-plus-gap-one 'inverse-times-gap-one
             'shape 'offset-shape 'positive-rows 'bounded-sums 'fixed)
            scaled-threshold-bound
            (app (function/const* 'signed/multiply-left-monotone [])
                 'inverse residual-distance 'threshold
                 'inverse-nonnegative 'residual-at-most-threshold)]
        (order-transitive
         distance (smul 'inverse residual-distance)
         (smul 'inverse 'threshold)
         residual-bound scaled-threshold-bound)))}))

(def definition-specs [])
(def theorem-specs
  [inverse-gap-residual-bound-spec
   affine-inverse-gap-fixed-point-residual-bound-spec
   affine-inverse-gap-stopping-certificate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-inverse-gap-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-inverse-gap-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
