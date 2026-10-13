(ns rainbow.math.linear.matrix.affine-general-rate-tail-certificate
  "Sharp fixed-point-free tail certificates at arbitrary rational rates.

  For canonical `gamma=a/(a+g)`, exact residual decay supplies a computable
  envelope at each iteration horizon.  Applying sharp two-candidate stability
  to horizons m and n gives

      d(x_m,x_n)
        <= ((a+g)/g) * (gamma^m*r_0 + gamma^n*r_0),

  where `r_0=d(x_0,x_1)`.  This is a finite Cauchy certificate that requires
  neither an exact fixed point nor a completeness axiom.  A threshold corollary
  exposes a direct stopping condition.  Theorem-only, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-general-rate-iterate-certificate
             :as iterate-certificate]
            [rainbow.math.linear.matrix.affine-inverse-gap-stability
             :as stability]
            [rainbow.math.linear.matrix.affine-tail-diameter :as tail]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.add-associative :as associative]))

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
(defn- power-scale [gamma steps value]
  (app (function/const* 'signed/nnrat-power-scale [])
       gamma steps value))
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
(defn- rate [ap gp]
  (make (succ ap) (nadd ap (succ gp))))
(defn- inverse [ap gp]
  (make (nadd (succ ap) (succ gp)) gp))
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

(defn- tail-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['ap nat] ['gp nat]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows
                        (from-nnrat (rate 'ap 'gp)))]
     ['left-steps nat] ['right-steps nat]]))

(def affine-general-rate-tail-bound-spec
  (let [gamma (rate 'ap 'gp)
        inverse-value (inverse 'ap 'gp)
        first-image (affine-action 'rows 'offset 'initial)
        initial-residual (sup-distance 'initial first-image)
        left-at (affine-iterate 'rows 'offset 'left-steps 'initial)
        right-at (affine-iterate 'rows 'offset 'right-steps 'initial)
        left-successor
        (affine-iterate 'rows 'offset (succ 'left-steps) 'initial)
        right-successor
        (affine-iterate 'rows 'offset (succ 'right-steps) 'initial)
        left-image (affine-action 'rows 'offset left-at)
        right-image (affine-action 'rows 'offset right-at)
        left-envelope (power-scale gamma 'left-steps initial-residual)
        right-envelope (power-scale gamma 'right-steps initial-residual)
        aggregate (sadd left-envelope right-envelope)]
    {:name 'matrix/affine-general-rate-iterate-tail-bound
     :universes []
     :type
     (function/forall
      (tail-binders)
      (sle (sup-distance left-at right-at)
           (smul (from-nnrat inverse-value) aggregate)))
     :value
     (function/lam
      (tail-binders)
      (let [pair-shape
            (app
             (function/const* 'matrix/affine-iterates-same-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape
             'left-steps 'right-steps)
            left-residual-shape
            (app
             (function/const* 'matrix/affine-iterate-residual-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape
             'left-steps)
            right-current-image-shape
            (app
             (function/const* 'matrix/affine-iterate-residual-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape
             'right-steps)
            right-residual-shape
            (shape-symmetric
             right-at right-image right-current-image-shape)
            left-action-shape
            (app
             (function/const* 'matrix/vector-multiply-output-shape [])
             'rows 'initial left-at)
            left-offset-shape
            (shape-transitive
             'offset (action 'rows 'initial) (action 'rows left-at)
             'offset-shape left-action-shape)
            left-successive-bound
            (app
             (function/const*
              'matrix/affine-nnrat-successive-residual-rate [])
             'rows 'offset 'initial gamma
             'step-shape 'offset-shape
             'positive-rows 'bounded-sums 'left-steps)
            left-successor-unfold
            (app (function/const* 'matrix/affine-iterate-successor [])
                 'rows 'offset 'left-steps 'initial)
            left-residual-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             left-at left-successor left-image left-successor-unfold)
            left-residual-bound
            (order-respects
             (sup-distance left-at left-successor)
             (sup-distance left-at left-image)
             left-envelope left-envelope
             left-residual-same (signed-reflexive left-envelope)
             left-successive-bound)
            right-successive-bound
            (app
             (function/const*
              'matrix/affine-nnrat-successive-residual-rate [])
             'rows 'offset 'initial gamma
             'step-shape 'offset-shape
             'positive-rows 'bounded-sums 'right-steps)
            right-successor-unfold
            (app (function/const* 'matrix/affine-iterate-successor [])
                 'rows 'offset 'right-steps 'initial)
            right-forward-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             right-at right-successor right-image
             right-successor-unfold)
            right-forward-bound
            (order-respects
             (sup-distance right-at right-successor)
             (sup-distance right-at right-image)
             right-envelope right-envelope
             right-forward-same (signed-reflexive right-envelope)
             right-successive-bound)
            right-residual-bound
            (order-respects
             (sup-distance right-at right-image)
             (sup-distance right-image right-at)
             right-envelope right-envelope
             (app (function/const* 'vector/sup-distance-symmetric [])
                  right-at right-image)
             (signed-reflexive right-envelope)
             right-forward-bound)]
        (app
         (function/const*
          'matrix/affine-general-rate-two-threshold-certificate [])
         'rows 'offset left-at right-at 'ap 'gp
         pair-shape left-residual-shape right-residual-shape
         left-offset-shape 'positive-rows 'bounded-sums
         left-envelope right-envelope
         left-residual-bound right-residual-bound)))}))

(def affine-general-rate-tail-stopping-spec
  (let [gamma (rate 'ap 'gp)
        inverse-value (inverse 'ap 'gp)
        first-image (affine-action 'rows 'offset 'initial)
        initial-residual (sup-distance 'initial first-image)
        left-at (affine-iterate 'rows 'offset 'left-steps 'initial)
        right-at (affine-iterate 'rows 'offset 'right-steps 'initial)
        left-envelope (power-scale gamma 'left-steps initial-residual)
        right-envelope (power-scale gamma 'right-steps initial-residual)
        scaled-aggregate
        (smul (from-nnrat inverse-value)
              (sadd left-envelope right-envelope))
        binders
        (into
         (tail-binders)
         [['threshold signed]
          ['tail-envelope-at-most-threshold
           (sle scaled-aggregate 'threshold)]])]
    {:name 'matrix/affine-general-rate-iterate-tail-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance left-at right-at) 'threshold))
     :value
     (function/lam
      binders
      (let [tail-bound
            (app
             (function/const*
              'matrix/affine-general-rate-iterate-tail-bound [])
             'rows 'offset 'initial 'ap 'gp
             'step-shape 'offset-shape 'positive-rows 'bounded-sums
             'left-steps 'right-steps)]
        (order-transitive
         (sup-distance left-at right-at)
         scaled-aggregate 'threshold
         tail-bound 'tail-envelope-at-most-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [affine-general-rate-tail-bound-spec
   affine-general-rate-tail-stopping-spec])

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
  '[rainbow.math.linear.matrix.affine-general-rate-iterate-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/add-associative :signed-add-associative associative/add-associative-spec) (extend-specs-if-missing :finite-matrix-affine-inverse-gap-stability stability/theorem-specs) (extend-spec-if-missing 'matrix/affine-iterate-preserves-initial-shape :finite-matrix-affine-tail-diameter tail/affine-iterate-preserves-initial-shape-spec) (extend-spec-if-missing 'matrix/affine-iterates-same-shape :finite-matrix-affine-tail-diameter tail/affine-iterates-same-shape-spec) (extend-spec-if-missing 'matrix/affine-iterate-residual-shape :finite-matrix-affine-tail-diameter tail/affine-iterate-residual-shape-spec) (support/extend-with :finite-matrix-affine-general-rate-tail-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-general-rate-tail-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
