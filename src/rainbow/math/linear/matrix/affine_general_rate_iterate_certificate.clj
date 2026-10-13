(ns rainbow.math.linear.matrix.affine-general-rate-iterate-certificate
  "Sharp finite-horizon iterate error at every canonical rational rate.

  Exact NNRAT residual decay already proves

      d(x_n,x_(n+1)) <= gamma^n * d(x_0,x_1)

  for an arbitrary row-sum rate gamma.  This module combines that computable
  envelope with the canonical inverse-gap certificate for
  `gamma=a/(a+g)`, `a=ap+1`, `g=gp+1`, yielding

      d(x_n,x*) <= ((a+g)/g) * gamma^n * d(x_0,x_1).

  Unlike the older exact-rate error theorem, no `gamma <= 1/2` premise is
  needed and the factor is sharp.  An explicit stopping corollary accepts any
  threshold above the scaled envelope.  Theorem-only, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-general-rate-certificate
             :as general-rate]
            [rainbow.math.linear.matrix.affine-inverse-gap-certificate
             :as inverse-gap]
            [rainbow.math.linear.matrix.affine-nnrat-exact-rate
             :as exact-rate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.geometric-bridge :as bridge]))

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

(defn- iterate-binders []
  [['rows matrix-type] ['offset vector-type]
   ['initial vector-type] ['fixed-point vector-type]
   ['ap nat] ['gp nat]
   ['shape (same-shape 'initial 'fixed-point)]
   ['offset-shape (same-shape 'offset (action 'rows 'initial))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows
                      (from-nnrat (rate 'ap 'gp)))]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]
   ['steps nat]])

(def affine-general-rate-iterate-error-spec
  (let [gamma (rate 'ap 'gp)
        inverse-value (inverse 'ap 'gp)
        first-image (affine-action 'rows 'offset 'initial)
        fixed-image (affine-action 'rows 'offset 'fixed-point)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        successor-current
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        residual-at (sup-distance current successor-current)
        envelope
        (power-scale
         gamma 'steps (sup-distance 'initial first-image))
        distance (sup-distance current 'fixed-point)]
    {:name 'matrix/affine-general-rate-iterate-error-exact-envelope
     :universes []
     :type
     (function/forall
      (iterate-binders)
      (sle distance (smul (from-nnrat inverse-value) envelope)))
     :value
     (function/lam
      (iterate-binders)
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
             'rows 'offset 'initial gamma
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
          'matrix/affine-general-rate-stopping-certificate [])
         'rows 'offset current 'fixed-point 'ap 'gp
         current-shape current-offset-shape
         'positive-rows 'bounded-sums 'fixed
         envelope computable-residual-rate)))}))

(def affine-general-rate-iterate-stopping-spec
  (let [gamma (rate 'ap 'gp)
        inverse-value (inverse 'ap 'gp)
        first-image (affine-action 'rows 'offset 'initial)
        current (affine-iterate 'rows 'offset 'steps 'initial)
        envelope
        (power-scale
         gamma 'steps (sup-distance 'initial first-image))
        scaled-envelope (smul (from-nnrat inverse-value) envelope)
        binders
        (into
         (iterate-binders)
         [['threshold signed]
          ['envelope-at-most-threshold
           (sle scaled-envelope 'threshold)]])]
    {:name 'matrix/affine-general-rate-iterate-stopping-certificate
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
              'matrix/affine-general-rate-iterate-error-exact-envelope [])
             'rows 'offset 'initial 'fixed-point 'ap 'gp
             'shape 'offset-shape 'positive-rows 'bounded-sums
             'fixed 'steps)]
        (order-transitive
         (sup-distance current 'fixed-point)
         scaled-envelope 'threshold
         finite-error 'envelope-at-most-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [affine-general-rate-iterate-error-spec
   affine-general-rate-iterate-stopping-spec])

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
  '[rainbow.math.linear.matrix.affine-nnrat-exact-rate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/from-nnrat-respects-equivalence :signed-geometric-bridge bridge/from-nnrat-respects-equivalence-spec) (extend-spec-if-missing 'signed/from-nnrat-multiply :signed-geometric-bridge bridge/from-nnrat-multiply-spec) (extend-specs-if-missing :finite-matrix-affine-inverse-gap-certificate inverse-gap/theorem-specs) (extend-specs-if-missing :finite-matrix-affine-general-rate-certificate general-rate/theorem-specs) (support/extend-with :finite-matrix-affine-general-rate-iterate-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-general-rate-iterate-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
