(ns rainbow.math.linear.matrix.affine-residual-decay
  "Geometric decay and finite-horizon error bounds from computable residuals.

  Iterating from `F(x0)` for n steps is equivalent to the successor iterate
  from `x0`.  Applying paired-trajectory contraction to those two initial
  states therefore proves

      d(x_n,x_(n+1)) <= (1/2)^n d(x_0,x_1).

  Combining this with the a posteriori residual certificate bounds the error
  of `x_n` using only the initial residual and the chosen horizon.  Practical
  corollaries accept actual-row NNRAT bounds gamma <= 1/2.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-iterate :as iterate]
            [rainbow.math.linear.matrix.affine-residual-certificate
             :as certificate]
            [rainbow.math.linear.matrix.affine-trajectory-order
             :as trajectory]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
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
(defn- succ [value] (app successor value))
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
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
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
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- half-residual-rate-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows signed-half)]
     ['steps nat]]))

(def affine-half-iterate-successive-residual-rate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        left-at (affine-iterate 'rows 'offset 'steps 'initial)
        paired-right
        (affine-iterate 'rows 'offset 'steps first-image)
        successor-at
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        paired-distance (sup-distance left-at paired-right)
        residual-at (sup-distance left-at successor-at)
        initial-residual (sup-distance 'initial first-image)
        envelope (half-power-scale 'steps initial-residual)]
    {:name 'matrix/affine-half-iterate-successive-residual-rate
     :universes []
     :type
     (function/forall
      (half-residual-rate-binders)
      (sle residual-at envelope))
     :value
     (function/lam
      (half-residual-rate-binders)
      (let [paired-rate
            (app
             (function/const*
              'matrix/affine-half-iterate-sup-distance-rate [])
             'rows 'offset 'initial first-image
             'step-shape 'offset-shape
             'positive-rows 'bounded-sums 'steps)
            shift
            (app (function/const* 'matrix/affine-iterate-shift [])
                 'rows 'offset 'initial 'steps)
            distance-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             left-at paired-right successor-at shift)]
        (order-respects
         paired-distance residual-at envelope envelope
         distance-same (signed-reflexive envelope) paired-rate)))}))

(defn- strong-residual-rate-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat 'gamma))]
     ['steps nat]]))

(def affine-strong-row-successive-residual-rate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        residual-at
        (sup-distance
         (affine-iterate 'rows 'offset 'steps 'initial)
         (affine-iterate 'rows 'offset (succ 'steps) 'initial))
        envelope
        (half-power-scale
         'steps (sup-distance 'initial first-image))]
    {:name 'matrix/affine-nnrat-strong-row-successive-residual-rate
     :universes []
     :type
     (function/forall
      (strong-residual-rate-binders)
      (sle residual-at envelope))
     :value
     (function/lam
      (strong-residual-rate-binders)
      (app
       (function/const*
        'matrix/affine-half-iterate-successive-residual-rate [])
       'rows 'offset 'initial
       'step-shape 'offset-shape 'positive-rows
       (app
        (function/const* 'matrix/nnrat-row-sums-imply-half-bound [])
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'steps))}))

(defn- iterate-error-binders []
  [['rows matrix-type] ['offset vector-type]
   ['initial vector-type] ['fixed-point vector-type]
   ['gamma nnrat]
   ['gamma-at-most-half (rle 'gamma nnrat-half)]
   ['shape (same-shape 'initial 'fixed-point)]
   ['offset-shape (same-shape 'offset (action 'rows 'initial))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat 'gamma))]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]
   ['steps nat]])

(def affine-strong-row-iterate-error-from-initial-residual-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        fixed-image (affine-action 'rows 'offset 'fixed-point)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        successor-current
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        residual-at (sup-distance current successor-current)
        initial-residual (sup-distance 'initial first-image)
        envelope (half-power-scale 'steps initial-residual)
        distance (sup-distance current 'fixed-point)]
    {:name 'matrix/affine-nnrat-strong-row-iterate-error-from-initial-residual
     :universes []
     :type
     (function/forall
      (iterate-error-binders)
      (sle distance (sadd envelope envelope)))
     :value
     (function/lam
      (iterate-error-binders)
      (let [image-pair-shape
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'offset 'initial 'fixed-point 'offset-shape)
            fixed-image-shape
            (app
             (function/const* 'vector/equivalent-implies-same-shape [])
             fixed-image 'fixed-point 'fixed)
            image-fixed-shape
            (shape-transitive
             first-image fixed-image 'fixed-point
             image-pair-shape fixed-image-shape)
            step-shape
            (shape-transitive
             'initial 'fixed-point first-image
             'shape
             (shape-symmetric
              first-image 'fixed-point image-fixed-shape))
            fixed-at
            (affine-iterate 'rows 'offset 'steps 'fixed-point)
            current-paired-shape
            (app
             (function/const* 'matrix/affine-iterate-output-shape [])
             'rows 'offset 'initial 'fixed-point
             'shape 'offset-shape 'steps)
            fixed-at-fixed
            (app
             (function/const* 'matrix/affine-iterate-fixed-point [])
             'rows 'offset 'fixed-point 'fixed 'steps)
            fixed-at-shape
            (app
             (function/const* 'vector/equivalent-implies-same-shape [])
             fixed-at 'fixed-point fixed-at-fixed)
            current-shape
            (shape-transitive
             current fixed-at 'fixed-point
             current-paired-shape fixed-at-shape)
            current-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'rows 'initial current)
            current-offset-shape
            (shape-transitive
             'offset (action 'rows 'initial) (action 'rows current)
             'offset-shape current-action-shape)
            residual-rate
            (app
             (function/const*
              'matrix/affine-nnrat-strong-row-successive-residual-rate [])
             'rows 'offset 'initial 'gamma 'gamma-at-most-half
             step-shape 'offset-shape
             'positive-rows 'bounded-sums 'steps)
            successor-unfold
            (app (function/const* 'matrix/affine-iterate-successor [])
                 'rows 'offset 'steps 'initial)
            current-residual-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             current successor-current
             (affine-action 'rows 'offset current)
             successor-unfold)
            computable-residual-rate
            (order-respects
             residual-at
             (sup-distance
              current (affine-action 'rows 'offset current))
             envelope envelope
             current-residual-same (signed-reflexive envelope)
             residual-rate)]
        (app
         (function/const*
          'matrix/affine-nnrat-strong-row-stopping-certificate [])
         'rows 'offset current 'fixed-point
         'gamma 'gamma-at-most-half
         current-shape current-offset-shape
         'positive-rows 'bounded-sums 'fixed
         envelope computable-residual-rate)))}))

(def affine-strong-row-iterate-stopping-certificate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        envelope (half-power-scale
                  'steps (sup-distance 'initial first-image))
        doubled-envelope (sadd envelope envelope)
        binders
        (into
         (iterate-error-binders)
         [['threshold signed]
          ['envelope-at-most-threshold
           (sle doubled-envelope 'threshold)]])]
    {:name 'matrix/affine-nnrat-strong-row-iterate-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance current 'fixed-point) 'threshold))
     :value
     (function/lam
      binders
      (let [finite-error
            (app
             (function/const*
              'matrix/affine-nnrat-strong-row-iterate-error-from-initial-residual [])
             'rows 'offset 'initial 'fixed-point
             'gamma 'gamma-at-most-half
             'shape 'offset-shape 'positive-rows 'bounded-sums
             'fixed 'steps)]
        (order-transitive
         (sup-distance current 'fixed-point)
         doubled-envelope 'threshold
         finite-error 'envelope-at-most-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [affine-half-iterate-successive-residual-rate-spec
   affine-strong-row-successive-residual-rate-spec
   affine-strong-row-iterate-error-from-initial-residual-spec
   affine-strong-row-iterate-stopping-certificate-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'matrix/affine-iterate-successor :finite-matrix-affine-iterate iterate/affine-iterate-successor-spec) (extend-spec-if-missing 'matrix/affine-iterate-shift :finite-matrix-affine-trajectory-order trajectory/affine-iterate-shift-spec) (support/extend-with :finite-matrix-affine-residual-decay theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-residual-decay))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
