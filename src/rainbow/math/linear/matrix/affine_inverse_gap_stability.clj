(ns rainbow.math.linear.matrix.affine-inverse-gap-stability
  "Sharp stability of two approximate affine solutions at arbitrary rates.

  For a reference affine map F with row-sum rate `q`, two candidates obey the
  quotient-safe inverse-gap bound

      d(x,y) <= inverse * (d(x,Fx) + d(Fy,y)),

  whenever `q + gap ~ 1` and `inverse * gap ~ 1`.  A bridged form replaces
  `d(Fy,y)` by `d(Fy,Gy) + d(Gy,y)`, allowing comparison against an arbitrary
  second model without requiring that model to contract.

  Canonical wrappers instantiate `q=a/(a+g)` and
  `inverse=(a+g)/g` for every positive naturals `a=ap+1`, `g=gp+1`.
  Thus independently implemented solvers and perturbed models receive the
  sharp rational factor without a `q <= 1/2` premise.  Theorem-only,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-general-rate-certificate
             :as general-rate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.add-associative :as associative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
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

(defn- inverse-gap-binders []
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)]
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rate signed] ['gap signed] ['inverse signed]
     ['rate-nonnegative (sle signed-zero 'rate)]
     ['inverse-nonnegative (sle signed-zero 'inverse)]
     ['rate-plus-gap-one
      (veq (sadd 'rate 'gap) signed-one)]
     ['inverse-times-gap-one
      (veq (smul 'inverse 'gap) signed-one)]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'rate)]]))

(def affine-inverse-gap-approximate-stability-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        distance (sup-distance 'left 'right)
        left-residual (sup-distance 'left left-image)
        image-distance (sup-distance left-image right-image)
        right-residual (sup-distance right-image 'right)
        left-image-to-right (sup-distance left-image 'right)
        residual-sum (sadd left-residual right-residual)
        scaled-distance (smul 'rate distance)
        three-segment
        (sadd left-residual (sadd image-distance right-residual))
        reordered (sadd residual-sum image-distance)]
    {:name 'matrix/affine-inverse-gap-approximate-stability
     :universes []
     :type
     (function/forall
      (inverse-gap-binders)
      (sle distance (smul 'inverse residual-sum)))
     :value
     (function/lam
      (inverse-gap-binders)
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
             'rows 'offset 'left 'right 'rate
             'rate-nonnegative
             'shape 'offset-shape 'positive-rows 'bounded-sums)
            contract-middle
            (add-monotone
             residual-sum residual-sum
             image-distance scaled-distance
             (order-reflexive residual-sum) contraction)
            self-bound
            (order-transitive
             distance reordered (sadd residual-sum scaled-distance)
             reordered-bound contract-middle)]
        (app
         (function/const* 'signed/inverse-gap-residual-bound [])
         distance residual-sum 'rate 'gap 'inverse
         'inverse-nonnegative
         'rate-plus-gap-one 'inverse-times-gap-one self-bound)))}))

(def affine-inverse-gap-two-threshold-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        right-residual (sup-distance right-image 'right)
        residual-sum (sadd left-residual right-residual)
        threshold-sum (sadd 'left-threshold 'right-threshold)
        binders
        (into
         (inverse-gap-binders)
         [['left-threshold signed] ['right-threshold signed]
          ['left-residual-bound (sle left-residual 'left-threshold)]
          ['right-residual-bound (sle right-residual 'right-threshold)]])]
    {:name 'matrix/affine-inverse-gap-two-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (smul 'inverse threshold-sum)))
     :value
     (function/lam
      binders
      (let [residual-stability
            (app
             (function/const*
              'matrix/affine-inverse-gap-approximate-stability [])
             'rows 'offset 'left 'right 'rate 'gap 'inverse
             'rate-nonnegative 'inverse-nonnegative
             'rate-plus-gap-one 'inverse-times-gap-one
             'shape 'left-residual-shape 'right-residual-shape
             'offset-shape 'positive-rows 'bounded-sums)
            threshold-bound
            (add-monotone
             left-residual 'left-threshold
             right-residual 'right-threshold
             'left-residual-bound 'right-residual-bound)
            scaled-threshold-bound
            (app (function/const* 'signed/multiply-left-monotone [])
                 'inverse residual-sum threshold-sum
                 'inverse-nonnegative threshold-bound)]
        (order-transitive
         (sup-distance 'left 'right)
         (smul 'inverse residual-sum)
         (smul 'inverse threshold-sum)
         residual-stability scaled-threshold-bound)))}))

(defn- general-rate-binders []
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)]
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['ap nat] ['gp nat]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['right-residual-shape (same-shape right-image 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]]))

(def affine-general-rate-approximate-stability-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        residual-sum
        (sadd (sup-distance 'left left-image)
              (sup-distance right-image 'right))]
    {:name 'matrix/affine-general-rate-approximate-stability
     :universes []
     :type
     (function/forall
      (general-rate-binders)
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) residual-sum)))
     :value
     (function/lam
      (general-rate-binders)
      (let [rate-value (rate 'ap 'gp)
            gap-value (gap 'ap 'gp)
            inverse-value (inverse 'ap 'gp)]
        (app
         (function/const*
          'matrix/affine-inverse-gap-approximate-stability [])
         'rows 'offset 'left 'right
         (from-nnrat rate-value)
         (from-nnrat gap-value)
         (from-nnrat inverse-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              rate-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              inverse-value)
         (app (function/const* 'signed/general-rate-plus-gap-one [])
              'ap 'gp)
         (app (function/const* 'signed/general-inverse-times-gap-one [])
              'ap 'gp)
         'shape 'left-residual-shape 'right-residual-shape
         'offset-shape 'positive-rows 'bounded-sums)))}))

(def affine-general-rate-two-threshold-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        right-residual (sup-distance right-image 'right)
        threshold-sum (sadd 'left-threshold 'right-threshold)
        binders
        (into
         (general-rate-binders)
         [['left-threshold signed] ['right-threshold signed]
          ['left-residual-bound (sle left-residual 'left-threshold)]
          ['right-residual-bound (sle right-residual 'right-threshold)]])]
    {:name 'matrix/affine-general-rate-two-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) threshold-sum)))
     :value
     (function/lam
      binders
      (let [rate-value (rate 'ap 'gp)
            gap-value (gap 'ap 'gp)
            inverse-value (inverse 'ap 'gp)]
        (app
         (function/const*
          'matrix/affine-inverse-gap-two-threshold-certificate [])
         'rows 'offset 'left 'right
         (from-nnrat rate-value)
         (from-nnrat gap-value)
         (from-nnrat inverse-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              rate-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              inverse-value)
         (app (function/const* 'signed/general-rate-plus-gap-one [])
              'ap 'gp)
         (app (function/const* 'signed/general-inverse-times-gap-one [])
              'ap 'gp)
         'shape 'left-residual-shape 'right-residual-shape
         'offset-shape 'positive-rows 'bounded-sums
         'left-threshold 'right-threshold
         'left-residual-bound 'right-residual-bound)))}))

(defn- bridged-binders []
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)]
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['comparison-image vector-type]
     ['ap nat] ['gp nat]
     ['shape (same-shape 'left 'right)]
     ['left-residual-shape (same-shape 'left left-image)]
     ['bridge-shape (same-shape right-image 'comparison-image)]
     ['comparison-residual-shape
      (same-shape 'comparison-image 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]]))

(def affine-general-rate-bridged-threshold-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        bridge-distance (sup-distance right-image 'comparison-image)
        comparison-residual (sup-distance 'comparison-image 'right)
        right-residual (sup-distance right-image 'right)
        right-threshold
        (sadd 'bridge-threshold 'comparison-residual-threshold)
        threshold-sum (sadd 'left-threshold right-threshold)
        binders
        (into
         (bridged-binders)
         [['left-threshold signed]
          ['bridge-threshold signed]
          ['comparison-residual-threshold signed]
          ['left-residual-bound (sle left-residual 'left-threshold)]
          ['bridge-bound (sle bridge-distance 'bridge-threshold)]
          ['comparison-residual-bound
           (sle comparison-residual 'comparison-residual-threshold)]])]
    {:name 'matrix/affine-general-rate-bridged-threshold-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) threshold-sum)))
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
             right-threshold
             triangle right-threshold-bound)]
        (app
         (function/const*
          'matrix/affine-general-rate-two-threshold-certificate [])
         'rows 'offset 'left 'right 'ap 'gp
         'shape 'left-residual-shape right-residual-shape
         'offset-shape 'positive-rows 'bounded-sums
         'left-threshold right-threshold
         'left-residual-bound right-residual-bound)))}))

(def affine-general-rate-bridged-stability-spec
  (let [left-image (affine-action 'rows 'offset 'left)
        right-image (affine-action 'rows 'offset 'right)
        left-residual (sup-distance 'left left-image)
        bridge-distance (sup-distance right-image 'comparison-image)
        comparison-residual (sup-distance 'comparison-image 'right)
        aggregate
        (sadd left-residual (sadd bridge-distance comparison-residual))]
    {:name 'matrix/affine-general-rate-bridged-stability
     :universes []
     :type
     (function/forall
      (bridged-binders)
      (sle (sup-distance 'left 'right)
           (smul (from-nnrat (inverse 'ap 'gp)) aggregate)))
     :value
     (function/lam
      (bridged-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-bridged-threshold-certificate [])
       'rows 'offset 'left 'right 'comparison-image 'ap 'gp
       'shape 'left-residual-shape 'bridge-shape
       'comparison-residual-shape
       'offset-shape 'positive-rows 'bounded-sums
       left-residual bridge-distance comparison-residual
       (order-reflexive left-residual)
       (order-reflexive bridge-distance)
       (order-reflexive comparison-residual)))}))

(def definition-specs [])
(def theorem-specs
  [affine-inverse-gap-approximate-stability-spec
   affine-inverse-gap-two-threshold-spec
   affine-general-rate-approximate-stability-spec
   affine-general-rate-two-threshold-spec
   affine-general-rate-bridged-threshold-spec
   affine-general-rate-bridged-stability-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-general-rate-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/add-associative :signed-add-associative associative/add-associative-spec) (support/extend-with :finite-matrix-affine-inverse-gap-stability theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-inverse-gap-stability))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
