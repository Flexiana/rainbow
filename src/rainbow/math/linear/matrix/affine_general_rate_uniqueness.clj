(ns rainbow.math.linear.matrix.affine-general-rate-uniqueness
  "Fixed-point uniqueness for every canonical rational row-sum contraction.

  The scalar theorem constructs the collapse certificate missing from the
  generic row-sum geometry.  For `gamma=a/(a+g)`, a nonnegative distance with

      d <= gamma*d

  is treated as the zero-residual case of the inverse-gap theorem, yielding
  `d <= ((a+g)/g)*0 ~ 0`; antisymmetry then gives `d ~ 0`.

  Instantiating the existing affine row-sum uniqueness interface removes the
  practical `gamma <= 1/2` restriction from exact fixed-point uniqueness.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-general-rate-certificate
             :as general-rate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as limit-uniqueness]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
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
(defn- rate [ap gp]
  (make (succ ap) (nadd ap (succ gp))))
(defn- gap [ap gp]
  (make (succ gp) (nadd ap (succ gp))))
(defn- inverse [ap gp]
  (make (nadd (succ ap) (succ gp)) gp))
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))

(def general-rate-contraction-collapse-spec
  {:name 'signed/general-rate-contraction-collapse :universes []
   :type
   (function/forall
    [['ap nat] ['gp nat] ['distance signed]
     ['distance-nonnegative (sle signed-zero 'distance)]
     ['self-bound
      (sle 'distance
           (smul (from-nnrat (rate 'ap 'gp)) 'distance))]]
    (veq 'distance signed-zero))
   :value
   (function/lam
    [['ap nat] ['gp nat] ['distance signed]
     ['distance-nonnegative (sle signed-zero 'distance)]
     ['self-bound
      (sle 'distance
           (smul (from-nnrat (rate 'ap 'gp)) 'distance))]]
    (let [rate-value (from-nnrat (rate 'ap 'gp))
          gap-value (from-nnrat (gap 'ap 'gp))
          inverse-value (from-nnrat (inverse 'ap 'gp))
          scaled-distance (smul rate-value 'distance)
          padded (sadd signed-zero scaled-distance)
          padded-scaled
          (signed-transitive
           padded (sadd scaled-distance signed-zero) scaled-distance
           (app (function/const* 'signed/add-commutative [])
                signed-zero scaled-distance)
           (app (function/const* 'signed/add-zero-right [])
                scaled-distance))
          padded-self-bound
          (order-respects
           'distance 'distance scaled-distance padded
           (signed-reflexive 'distance)
           (signed-symmetric padded scaled-distance padded-scaled)
           'self-bound)
          inverse-zero-bound
          (app
           (function/const* 'signed/inverse-gap-residual-bound [])
           'distance signed-zero rate-value gap-value inverse-value
           (app (function/const* 'signed/zero-at-most-from-nnrat [])
                (inverse 'ap 'gp))
           (app (function/const* 'signed/general-rate-plus-gap-one [])
                'ap 'gp)
           (app (function/const* 'signed/general-inverse-times-gap-one [])
                'ap 'gp)
           padded-self-bound)
          inverse-zero
          (app (function/const* 'signed/multiply-zero-right [])
               inverse-value)
          distance-at-most-zero
          (order-respects
           'distance 'distance
           (smul inverse-value signed-zero) signed-zero
           (signed-reflexive 'distance) inverse-zero
           inverse-zero-bound)]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'distance signed-zero
           distance-at-most-zero 'distance-nonnegative)))})

(defn- fixed-binders []
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] ['right vector-type]
   ['ap nat] ['gp nat]
   ['shape (same-shape 'left 'right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows
                      (from-nnrat (rate 'ap 'gp)))]
   ['left-fixed
    (vector-equivalent (affine-action 'rows 'offset 'left) 'left)]
   ['right-fixed
    (vector-equivalent (affine-action 'rows 'offset 'right) 'right)]])

(def affine-general-rate-fixed-points-zero-distance-spec
  {:name 'matrix/affine-general-rate-fixed-points-have-zero-sup-distance
   :universes []
   :type
   (function/forall
    (fixed-binders)
    (veq (sup-distance 'left 'right) signed-zero))
   :value
   (function/lam
    (fixed-binders)
    (let [rate-value (from-nnrat (rate 'ap 'gp))
          collapse
          (function/lam
           [['distance signed]
            ['distance-nonnegative (sle signed-zero 'distance)]
            ['self-bound
             (sle 'distance (smul rate-value 'distance))]]
           (app
            (function/const* 'signed/general-rate-contraction-collapse [])
            'ap 'gp 'distance 'distance-nonnegative 'self-bound))]
      (app
       (function/const*
        'matrix/affine-row-sum-fixed-points-have-zero-sup-distance [])
       'rows 'offset 'left 'right rate-value
       (app (function/const* 'signed/zero-at-most-from-nnrat [])
            (rate 'ap 'gp))
       'shape 'offset-shape 'positive-rows 'bounded-sums
       'left-fixed 'right-fixed collapse)))})

(def affine-general-rate-fixed-points-unique-spec
  {:name 'matrix/affine-general-rate-fixed-points-unique :universes []
   :type
   (function/forall (fixed-binders) (vector-equivalent 'left 'right))
   :value
   (function/lam
    (fixed-binders)
    (let [rate-value (from-nnrat (rate 'ap 'gp))
          collapse
          (function/lam
           [['distance signed]
            ['distance-nonnegative (sle signed-zero 'distance)]
            ['self-bound
             (sle 'distance (smul rate-value 'distance))]]
           (app
            (function/const* 'signed/general-rate-contraction-collapse [])
            'ap 'gp 'distance 'distance-nonnegative 'self-bound))]
      (app
       (function/const* 'matrix/affine-row-sum-fixed-points-unique [])
       'rows 'offset 'left 'right rate-value
       (app (function/const* 'signed/zero-at-most-from-nnrat [])
            (rate 'ap 'gp))
       'shape 'offset-shape 'positive-rows 'bounded-sums
       'left-fixed 'right-fixed collapse)))})

(def definition-specs [])
(def theorem-specs
  [general-rate-contraction-collapse-spec
   affine-general-rate-fixed-points-zero-distance-spec
   affine-general-rate-fixed-points-unique-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      general-rate/extend-environment
      (extend-spec-if-missing
       'signed/add-zero-right
       :signed-limit-uniqueness
       limit-uniqueness/signed-add-zero-right-spec)
      (extend-spec-if-missing
       'signed/at-most-antisymmetric
       :signed-limit-uniqueness
       limit-uniqueness/signed-at-most-antisymmetric-spec)
      (extend-spec-if-missing
       'signed/multiply-zero-right
       :signed-multiply-ring
       multiply-ring/multiply-zero-right-spec)
      (support/extend-with
       :finite-matrix-affine-general-rate-uniqueness theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
