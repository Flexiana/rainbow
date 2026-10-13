(ns rainbow.math.linear.matrix.affine-tail-diameter
  "Constructive tail diameter for contractive affine iteration.

  Shape preservation is factored into reusable lemmas: every iterate has the
  initial vector's shape, all horizons therefore share a shape, and each
  iterate has the shape of its affine image.  Combining those facts with
  eventual residual certificates and approximate-solution stability proves

      k <= m, k <= n  =>  d(x_m,x_n) <= 4 * from-nnrat(harmonic k).

  This is a computable Cauchy-style tail certificate that assumes no supplied
  exact fixed point or completeness principle.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-approximate-fixed-point
             :as approximate]
            [rainbow.math.linear.matrix.affine-approximate-stability
             :as stability]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.add-associative :as associative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-one (function/const* 'signed/one []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
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
(defn- row-sums-bounded [rows gamma]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) (from-nnrat gamma))))
(defn- harmonic-radius [index]
  (from-nnrat (app (function/const* 'nnrat/harmonic []) index)))
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))
(defn- shape-reflexive [values]
  (app (function/const* 'vector/same-shape-reflexive []) values))
(defn- shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))

(defn- shape-binders [include-steps?]
  (let [first-image (affine-action 'rows 'offset 'initial)
        base
        [['rows matrix-type] ['offset vector-type] ['initial vector-type]
         ['step-shape (same-shape 'initial first-image)]
         ['offset-shape (same-shape 'offset (action 'rows 'initial))]]]
    (if include-steps?
      (conj base ['steps nat])
      base)))

(def affine-iterate-preserves-initial-shape-spec
  {:name 'matrix/affine-iterate-preserves-initial-shape :universes []
   :type
   (function/forall
    (shape-binders true)
    (same-shape
     'initial (affine-iterate 'rows 'offset 'steps 'initial)))
   :value
   (function/lam
    (shape-binders true)
    (let [at (fn [n] (affine-iterate 'rows 'offset n 'initial))
          motive
          (function/lam
           [['n nat]] (same-shape 'initial (at 'n)))
          step
          (function/lam
           [['n nat] ['previous-shape (app motive 'n)]]
           (shape-transitive
            'initial
            (affine-action 'rows 'offset 'initial)
            (affine-action 'rows 'offset (at 'n))
            'step-shape
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'offset 'initial (at 'n) 'offset-shape)))]
      (prop-nat-rec motive (shape-reflexive 'initial) step 'steps)))})

(def affine-iterates-same-shape-spec
  (let [binders
        (into (shape-binders false)
              [['left-steps nat] ['right-steps nat]])
        left-at (affine-iterate 'rows 'offset 'left-steps 'initial)
        right-at (affine-iterate 'rows 'offset 'right-steps 'initial)]
    {:name 'matrix/affine-iterates-same-shape :universes []
     :type (function/forall binders (same-shape left-at right-at))
     :value
     (function/lam
      binders
      (let [left-shape
            (app
             (function/const*
              'matrix/affine-iterate-preserves-initial-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape 'left-steps)
            right-shape
            (app
             (function/const*
              'matrix/affine-iterate-preserves-initial-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape 'right-steps)]
        (shape-transitive
         left-at 'initial right-at
         (shape-symmetric 'initial left-at left-shape)
         right-shape)))}))

(def affine-iterate-residual-shape-spec
  (let [current (affine-iterate 'rows 'offset 'steps 'initial)
        current-image (affine-action 'rows 'offset current)
        first-image (affine-action 'rows 'offset 'initial)]
    {:name 'matrix/affine-iterate-residual-shape :universes []
     :type
     (function/forall
      (shape-binders true)
      (same-shape current current-image))
     :value
     (function/lam
      (shape-binders true)
      (let [initial-current
            (app
             (function/const*
              'matrix/affine-iterate-preserves-initial-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape 'steps)
            first-current-image
            (app
             (function/const* 'matrix/affine-action-output-shape [])
             'rows 'offset 'initial current 'offset-shape)
            initial-current-image
            (shape-transitive
             'initial first-image current-image
             'step-shape first-current-image)]
        (shape-transitive
         current 'initial current-image
         (shape-symmetric 'initial current initial-current)
         initial-current-image)))}))

(defn- tail-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'gamma)]
     ['initial-residual-at-most-one
      (sle (sup-distance 'initial first-image) signed-one)]
     ['index nat] ['left-steps nat] ['right-steps nat]
     ['left-large-enough (nat-at-most 'index 'left-steps)]
     ['right-large-enough (nat-at-most 'index 'right-steps)]]))

(def affine-iterate-tail-diameter-spec
  (let [left-at (affine-iterate 'rows 'offset 'left-steps 'initial)
        right-at (affine-iterate 'rows 'offset 'right-steps 'initial)
        left-image (affine-action 'rows 'offset left-at)
        right-image (affine-action 'rows 'offset right-at)
        radius (harmonic-radius 'index)
        twice-radius (sadd radius radius)]
    {:name 'matrix/affine-nnrat-iterate-tail-diameter :universes []
     :type
     (function/forall
      (tail-binders)
      (sle (sup-distance left-at right-at)
           (sadd twice-radius twice-radius)))
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
             'rows 'offset 'initial 'step-shape 'offset-shape 'left-steps)
            right-current-image-shape
            (app
             (function/const* 'matrix/affine-iterate-residual-shape [])
             'rows 'offset 'initial 'step-shape 'offset-shape 'right-steps)
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
            left-residual-bound
            (app
             (function/const*
              'matrix/affine-nnrat-eventually-approximate-fixed-point [])
             'rows 'offset 'initial 'gamma 'gamma-at-most-half
             'step-shape 'offset-shape 'positive-rows 'bounded-sums
             'initial-residual-at-most-one
             'index 'left-steps 'left-large-enough)
            right-forward-residual-bound
            (app
             (function/const*
              'matrix/affine-nnrat-eventually-approximate-fixed-point [])
             'rows 'offset 'initial 'gamma 'gamma-at-most-half
             'step-shape 'offset-shape 'positive-rows 'bounded-sums
             'initial-residual-at-most-one
             'index 'right-steps 'right-large-enough)
            right-residual-bound
            (order-respects
             (sup-distance right-at right-image)
             (sup-distance right-image right-at)
             radius radius
             (app (function/const* 'vector/sup-distance-symmetric [])
                  right-at right-image)
             (signed-reflexive radius)
             right-forward-residual-bound)]
        (app
         (function/const*
          'matrix/affine-nnrat-two-threshold-stability-certificate [])
         'rows 'offset left-at right-at
         'gamma 'gamma-at-most-half
         pair-shape left-residual-shape right-residual-shape
         left-offset-shape 'positive-rows 'bounded-sums
         radius radius left-residual-bound right-residual-bound)))}))

(def definition-specs [])
(def theorem-specs
  [affine-iterate-preserves-initial-shape-spec
   affine-iterates-same-shape-spec
   affine-iterate-residual-shape-spec
   affine-iterate-tail-diameter-spec])

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
  '[rainbow.math.linear.matrix.affine-approximate-fixed-point])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/add-associative :signed-add-associative associative/add-associative-spec) (extend-specs-if-missing :finite-matrix-affine-approximate-stability stability/theorem-specs) (support/extend-with :finite-matrix-affine-tail-diameter theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-tail-diameter))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
