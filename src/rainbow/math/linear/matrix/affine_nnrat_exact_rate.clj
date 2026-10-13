(ns rainbow.math.linear.matrix.affine-nnrat-exact-rate
  "Exact NNRAT-rate contraction and residual certificates.

  `signed/nnrat-power-scale gamma n d` is the native signed recurrence
  `d, gamma*d, gamma*(gamma*d), ...`.  Unlike the conservative half envelope,
  it records the actual certified row-sum factor.  The matrix theorems prove
  exact gamma-power bounds for paired trajectories and successive residuals.
  When gamma <= 1/2, the a posteriori residual theorem then yields a fixed-point
  error certificate with the same exact envelope.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual-decay :as decay]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- nat-value-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [type-level])
       motive base step value))
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
(defn- rate-nonnegative [gamma]
  (app (function/const* 'signed/zero-at-most-from-nnrat []) gamma))

(def nnrat-power-scale-spec
  {:name 'signed/nnrat-power-scale :kind :definition :universes []
   :type (function/arrow nnrat nat signed signed)
   :value
   (function/lam
    [['gamma nnrat] ['steps nat] ['value signed]]
    (nat-value-rec
     (function/lam [['ignored nat]] signed)
     'value
     (function/lam
      [['ignored-step nat] ['previous signed]]
      (smul (from-nnrat 'gamma) 'previous))
     'steps))})

(def nnrat-power-scale-zero-spec
  {:name 'signed/nnrat-power-scale-zero :universes []
   :type
   (function/forall
    [['gamma nnrat] ['value signed]]
    (veq (power-scale 'gamma nat-zero 'value) 'value))
   :value
   (function/lam
    [['gamma nnrat] ['value signed]]
    (signed-reflexive 'value))})

(def nnrat-power-scale-successor-spec
  {:name 'signed/nnrat-power-scale-successor :universes []
   :type
   (function/forall
    [['gamma nnrat] ['steps nat] ['value signed]]
    (veq
     (power-scale 'gamma (succ 'steps) 'value)
     (smul (from-nnrat 'gamma)
           (power-scale 'gamma 'steps 'value))))
   :value
   (function/lam
    [['gamma nnrat] ['steps nat] ['value signed]]
    (signed-reflexive
     (smul (from-nnrat 'gamma)
           (power-scale 'gamma 'steps 'value))))})

(def nnrat-power-scale-nonnegative-spec
  {:name 'signed/nnrat-power-scale-nonnegative :universes []
   :type
   (function/forall
    [['gamma nnrat] ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (sle signed-zero (power-scale 'gamma 'steps 'value)))
   :value
   (function/lam
    [['gamma nnrat] ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (sle signed-zero (power-scale 'gamma 'n 'value)))
          step
          (function/lam
           [['n nat] ['previous-nonnegative (app motive 'n)]]
           (let [rate (from-nnrat 'gamma)
                 previous (power-scale 'gamma 'n 'value)
                 product (smul rate previous)]
             (app
              (function/const* 'signed/zero-at-most-of-nonnegative [])
              product
              (app
               (function/const* 'signed/multiply-nonnegative [])
               rate previous
               (app
                (function/const* 'signed/nonnegative-of-zero-at-most [])
                rate (rate-nonnegative 'gamma))
               (app
                (function/const* 'signed/nonnegative-of-zero-at-most [])
                previous 'previous-nonnegative)))))]
      (prop-nat-rec motive 'value-nonnegative step 'steps)))})

(def nnrat-power-scale-monotone-spec
  {:name 'signed/nnrat-power-scale-monotone :universes []
   :type
   (function/forall
    [['gamma nnrat] ['left signed] ['right signed]
     ['ordered (sle 'left 'right)] ['steps nat]]
    (sle (power-scale 'gamma 'steps 'left)
         (power-scale 'gamma 'steps 'right)))
   :value
   (function/lam
    [['gamma nnrat] ['left signed] ['right signed]
     ['ordered (sle 'left 'right)] ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (sle (power-scale 'gamma 'n 'left)
                (power-scale 'gamma 'n 'right)))
          step
          (function/lam
           [['n nat] ['previous-ordered (app motive 'n)]]
           (app
            (function/const* 'signed/multiply-left-monotone [])
            (from-nnrat 'gamma)
            (power-scale 'gamma 'n 'left)
            (power-scale 'gamma 'n 'right)
            (rate-nonnegative 'gamma)
            'previous-ordered))]
      (prop-nat-rec motive 'ordered step 'steps)))})

(defn- paired-rate-binders []
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] ['right vector-type]
   ['gamma nnrat]
   ['shape (same-shape 'left 'right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat 'gamma))]
   ['steps nat]])

(def affine-nnrat-row-sum-iterate-sup-distance-rate-spec
  (let [distance-at
        (fn [n]
          (sup-distance
           (affine-iterate 'rows 'offset n 'left)
           (affine-iterate 'rows 'offset n 'right)))
        initial-distance (sup-distance 'left 'right)]
    {:name 'matrix/affine-nnrat-row-sum-iterate-sup-distance-rate
     :universes []
     :type
     (function/forall
      (paired-rate-binders)
      (sle (distance-at 'steps)
           (power-scale 'gamma 'steps initial-distance)))
     :value
     (function/lam
      (paired-rate-binders)
      (let [motive
            (function/lam
             [['n nat]]
             (sle (distance-at 'n)
                  (power-scale 'gamma 'n initial-distance)))
            step
            (function/lam
             [['n nat] ['previous-bound (app motive 'n)]]
             (let [left-current
                   (affine-iterate 'rows 'offset 'n 'left)
                   right-current
                   (affine-iterate 'rows 'offset 'n 'right)
                   previous-distance (distance-at 'n)
                   previous-envelope
                   (power-scale 'gamma 'n initial-distance)
                   next-envelope
                   (smul (from-nnrat 'gamma) previous-envelope)
                   current-shape
                   (app
                    (function/const* 'matrix/affine-iterate-output-shape [])
                    'rows 'offset 'left 'right
                    'shape 'offset-shape 'n)
                   current-action-shape
                   (app
                    (function/const* 'matrix/vector-multiply-output-shape [])
                    'rows 'left left-current)
                   current-offset-shape
                   (shape-transitive
                    'offset (action 'rows 'left)
                    (action 'rows left-current)
                    'offset-shape current-action-shape)
                   one-step
                   (app
                    (function/const*
                     'matrix/affine-action-row-sum-lipschitz [])
                    'rows 'offset left-current right-current
                    (from-nnrat 'gamma) (rate-nonnegative 'gamma)
                    current-shape current-offset-shape
                    'positive-rows 'bounded-sums)
                   scaled-bound
                   (app
                    (function/const* 'signed/multiply-left-monotone [])
                    (from-nnrat 'gamma)
                    previous-distance previous-envelope
                    (rate-nonnegative 'gamma) 'previous-bound)]
               (order-transitive
                (distance-at (succ 'n))
                (smul (from-nnrat 'gamma) previous-distance)
                next-envelope one-step scaled-bound)))]
        (prop-nat-rec
         motive
         (app (function/const* 'signed/at-most-reflexive [])
              initial-distance)
         step 'steps)))}))

(defn- residual-rate-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['gamma nnrat]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat 'gamma))]
     ['steps nat]]))

(def affine-nnrat-successive-residual-rate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        left-at (affine-iterate 'rows 'offset 'steps 'initial)
        paired-right (affine-iterate 'rows 'offset 'steps first-image)
        successor-at
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        paired-distance (sup-distance left-at paired-right)
        residual-at (sup-distance left-at successor-at)
        envelope
        (power-scale
         'gamma 'steps (sup-distance 'initial first-image))]
    {:name 'matrix/affine-nnrat-successive-residual-rate
     :universes []
     :type
     (function/forall
      (residual-rate-binders)
      (sle residual-at envelope))
     :value
     (function/lam
      (residual-rate-binders)
      (let [paired-rate
            (app
             (function/const*
              'matrix/affine-nnrat-row-sum-iterate-sup-distance-rate [])
             'rows 'offset 'initial first-image 'gamma
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

(defn- exact-error-binders []
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

(def affine-nnrat-strong-row-iterate-error-exact-rate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        fixed-image (affine-action 'rows 'offset 'fixed-point)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        successor-current
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        residual-at (sup-distance current successor-current)
        envelope
        (power-scale
         'gamma 'steps (sup-distance 'initial first-image))
        distance (sup-distance current 'fixed-point)]
    {:name 'matrix/affine-nnrat-strong-row-iterate-error-exact-rate
     :universes []
     :type
     (function/forall
      (exact-error-binders)
      (sle distance (sadd envelope envelope)))
     :value
     (function/lam
      (exact-error-binders)
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
              'matrix/affine-nnrat-successive-residual-rate [])
             'rows 'offset 'initial 'gamma
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

(def affine-nnrat-strong-row-stopping-exact-rate-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        envelope
        (power-scale
         'gamma 'steps (sup-distance 'initial first-image))
        doubled-envelope (sadd envelope envelope)
        binders
        (into
         (exact-error-binders)
         [['threshold signed]
          ['envelope-at-most-threshold
           (sle doubled-envelope 'threshold)]])]
    {:name 'matrix/affine-nnrat-strong-row-stopping-certificate-exact-rate
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
              'matrix/affine-nnrat-strong-row-iterate-error-exact-rate [])
             'rows 'offset 'initial 'fixed-point
             'gamma 'gamma-at-most-half
             'shape 'offset-shape 'positive-rows 'bounded-sums
             'fixed 'steps)]
        (order-transitive
         (sup-distance current 'fixed-point)
         doubled-envelope 'threshold
         finite-error 'envelope-at-most-threshold)))}))

(def definition-specs [nnrat-power-scale-spec])
(def theorem-specs
  [nnrat-power-scale-zero-spec
   nnrat-power-scale-successor-spec
   nnrat-power-scale-nonnegative-spec
   nnrat-power-scale-monotone-spec
   affine-nnrat-row-sum-iterate-sup-distance-rate-spec
   affine-nnrat-successive-residual-rate-spec
   affine-nnrat-strong-row-iterate-error-exact-rate-spec
   affine-nnrat-strong-row-stopping-exact-rate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-decay])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-nnrat-exact-rate (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-nnrat-exact-rate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
