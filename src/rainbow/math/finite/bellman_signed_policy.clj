(ns rainbow.math.finite.bellman-signed-policy
  "Signed-reward fixed-policy Bellman certificates in finite matrix form.

  A fixed policy over an explicitly enumerated state vector has the affine
  Bellman step `T(v) = reward + discounted-transition * v`. The reward vector
  is fully signed. Because the same reward occurs in both images, it cancels
  from sup distance; nonnegative transition rows with a canonical rational
  row-sum bound below one therefore give contraction, a sharp residual
  certificate, and fixed-point uniqueness.

  This bridges the signed affine development to Bellman policy evaluation. It
  does not cover max-over-actions Bellman optimality, fixed-point existence, or
  an executable solver. Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-general-rate-uniqueness
             :as uniqueness]
            [rainbow.math.linear.matrix.affine-general-rate-tail-certificate
             :as tail-certificate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

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
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
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
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows reward values]
  (app (function/const* 'matrix/affine-action []) rows reward values))
(defn- policy-step [rows reward values]
  (app (function/const* 'bellman/signed-policy-step []) rows reward values))
(defn- affine-iterate [rows reward steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows reward steps initial))
(defn- policy-iterate [rows reward steps initial]
  (app (function/const* 'bellman/signed-policy-iterate [])
       rows reward steps initial))
(defn- power-scale [gamma steps value]
  (app (function/const* 'signed/nnrat-power-scale []) gamma steps value))
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

(def signed-policy-step-spec
  {:name 'bellman/signed-policy-step
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type vector-type vector-type)
   :value
   (function/lam
    [['rows matrix-type] ['reward vector-type] ['values vector-type]]
    (affine-action 'rows 'reward 'values))})

(def signed-policy-iterate-spec
  {:name 'bellman/signed-policy-iterate
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type nat vector-type vector-type)
   :value
   (function/lam
    [['rows matrix-type] ['reward vector-type]
     ['steps nat] ['initial vector-type]]
    (affine-iterate 'rows 'reward 'steps 'initial))})

(def signed-policy-step-reward-cancels-distance-spec
  {:name 'bellman/signed-policy-step-reward-cancels-distance
   :universes []
   :type
   (function/forall
    [['rows matrix-type] ['reward vector-type]
     ['left vector-type] ['right vector-type]
     ['reward-shape (same-shape 'reward (action 'rows 'left))]]
    (veq
     (sup-distance (policy-step 'rows 'reward 'left)
                   (policy-step 'rows 'reward 'right))
     (sup-distance (action 'rows 'left) (action 'rows 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['reward vector-type]
     ['left vector-type] ['right vector-type]
     ['reward-shape (same-shape 'reward (action 'rows 'left))]]
    (app
     (function/const*
      'matrix/affine-action-sup-distance-cancels-offset [])
     'rows 'reward 'left 'right 'reward-shape))})

(defn- contraction-binders []
  [['rows matrix-type] ['reward vector-type]
   ['left vector-type] ['right vector-type]
   ['ap nat] ['gp nat]
   ['shape (same-shape 'left 'right)]
   ['reward-shape (same-shape 'reward (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]])

(def signed-policy-step-general-rate-contraction-spec
  (let [rate-value (from-nnrat (rate 'ap 'gp))]
    {:name 'bellman/signed-policy-step-general-rate-contraction
     :universes []
     :type
     (function/forall
      (contraction-binders)
      (sle
       (sup-distance (policy-step 'rows 'reward 'left)
                     (policy-step 'rows 'reward 'right))
       (smul rate-value (sup-distance 'left 'right))))
     :value
     (function/lam
      (contraction-binders)
      (app
       (function/const* 'matrix/affine-action-row-sum-lipschitz [])
       'rows 'reward 'left 'right rate-value
       (app (function/const* 'signed/zero-at-most-from-nnrat [])
            (rate 'ap 'gp))
       'shape 'reward-shape 'positive-rows 'bounded-sums))}))

(defn- fixed-binders []
  (into
   (contraction-binders)
   [['left-fixed
     (vector-equivalent (policy-step 'rows 'reward 'left) 'left)]
    ['right-fixed
     (vector-equivalent (policy-step 'rows 'reward 'right) 'right)]]))

(def signed-policy-fixed-points-unique-spec
  {:name 'bellman/signed-policy-fixed-points-unique
   :universes []
   :type (function/forall (fixed-binders) (vector-equivalent 'left 'right))
   :value
   (function/lam
    (fixed-binders)
    (app
     (function/const* 'matrix/affine-general-rate-fixed-points-unique [])
     'rows 'reward 'left 'right 'ap 'gp
     'shape 'reward-shape 'positive-rows 'bounded-sums
     'left-fixed 'right-fixed))})

(defn- residual-binders []
  [['rows matrix-type] ['reward vector-type]
   ['approximate vector-type] ['fixed-point vector-type]
   ['ap nat] ['gp nat]
   ['shape (same-shape 'approximate 'fixed-point)]
   ['reward-shape (same-shape 'reward (action 'rows 'approximate))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]
   ['fixed
    (vector-equivalent
     (policy-step 'rows 'reward 'fixed-point) 'fixed-point)]])

(def signed-policy-fixed-point-residual-bound-spec
  (let [image (policy-step 'rows 'reward 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)]
    {:name 'bellman/signed-policy-fixed-point-residual-bound
     :universes []
     :type
     (function/forall
      (residual-binders)
      (sle distance
           (smul (from-nnrat (inverse 'ap 'gp)) residual)))
     :value
     (function/lam
      (residual-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-fixed-point-residual-bound [])
       'rows 'reward 'approximate 'fixed-point 'ap 'gp
       'shape 'reward-shape 'positive-rows 'bounded-sums 'fixed))}))

(def signed-policy-fixed-point-stopping-certificate-spec
  (let [image (policy-step 'rows 'reward 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)
        binders
        (into
         (residual-binders)
         [['threshold signed]
          ['residual-at-most-threshold (sle residual 'threshold)]])]
    {:name 'bellman/signed-policy-fixed-point-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle distance
           (smul (from-nnrat (inverse 'ap 'gp)) 'threshold)))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-general-rate-stopping-certificate [])
       'rows 'reward 'approximate 'fixed-point 'ap 'gp
       'shape 'reward-shape 'positive-rows 'bounded-sums 'fixed
       'threshold 'residual-at-most-threshold))}))

(defn- iterate-binders []
  (into
   (residual-binders)
   [['steps nat]]))

(def signed-policy-iterate-error-exact-envelope-spec
  (let [gamma (rate 'ap 'gp)
        initial-image (policy-step 'rows 'reward 'approximate)
        current
        (policy-iterate 'rows 'reward 'steps 'approximate)
        envelope
        (power-scale
         gamma 'steps (sup-distance 'approximate initial-image))]
    {:name 'bellman/signed-policy-iterate-error-exact-envelope
     :universes []
     :type
     (function/forall
      (iterate-binders)
      (sle
       (sup-distance current 'fixed-point)
       (smul (from-nnrat (inverse 'ap 'gp)) envelope)))
     :value
     (function/lam
      (iterate-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-iterate-error-exact-envelope [])
       'rows 'reward 'approximate 'fixed-point 'ap 'gp
       'shape 'reward-shape 'positive-rows 'bounded-sums 'fixed 'steps))}))

(def signed-policy-iterate-stopping-certificate-spec
  (let [gamma (rate 'ap 'gp)
        initial-image (policy-step 'rows 'reward 'approximate)
        current
        (policy-iterate 'rows 'reward 'steps 'approximate)
        envelope
        (power-scale
         gamma 'steps (sup-distance 'approximate initial-image))
        scaled-envelope
        (smul (from-nnrat (inverse 'ap 'gp)) envelope)
        binders
        (into
         (iterate-binders)
         [['threshold signed]
          ['envelope-at-most-threshold
           (sle scaled-envelope 'threshold)]])]
    {:name 'bellman/signed-policy-iterate-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance current 'fixed-point) 'threshold))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-general-rate-iterate-stopping-certificate [])
       'rows 'reward 'approximate 'fixed-point 'ap 'gp
       'shape 'reward-shape 'positive-rows 'bounded-sums 'fixed 'steps
       'threshold 'envelope-at-most-threshold))}))

(defn- tail-binders []
  (let [first-image (policy-step 'rows 'reward 'initial)]
    [['rows matrix-type] ['reward vector-type] ['initial vector-type]
     ['ap nat] ['gp nat]
     ['step-shape (same-shape 'initial first-image)]
     ['reward-shape (same-shape 'reward (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]
     ['left-steps nat] ['right-steps nat]]))

(def signed-policy-iterate-tail-bound-spec
  (let [gamma (rate 'ap 'gp)
        first-image (policy-step 'rows 'reward 'initial)
        initial-residual (sup-distance 'initial first-image)
        left-at (policy-iterate 'rows 'reward 'left-steps 'initial)
        right-at (policy-iterate 'rows 'reward 'right-steps 'initial)
        left-envelope (power-scale gamma 'left-steps initial-residual)
        right-envelope (power-scale gamma 'right-steps initial-residual)]
    {:name 'bellman/signed-policy-iterate-tail-bound
     :universes []
     :type
     (function/forall
      (tail-binders)
      (sle
       (sup-distance left-at right-at)
       (smul
        (from-nnrat (inverse 'ap 'gp))
        (sadd left-envelope right-envelope))))
     :value
     (function/lam
      (tail-binders)
      (app
       (function/const*
        'matrix/affine-general-rate-iterate-tail-bound [])
       'rows 'reward 'initial 'ap 'gp
       'step-shape 'reward-shape 'positive-rows 'bounded-sums
       'left-steps 'right-steps))}))

(def signed-policy-iterate-tail-stopping-certificate-spec
  (let [gamma (rate 'ap 'gp)
        first-image (policy-step 'rows 'reward 'initial)
        initial-residual (sup-distance 'initial first-image)
        left-at (policy-iterate 'rows 'reward 'left-steps 'initial)
        right-at (policy-iterate 'rows 'reward 'right-steps 'initial)
        left-envelope (power-scale gamma 'left-steps initial-residual)
        right-envelope (power-scale gamma 'right-steps initial-residual)
        scaled-aggregate
        (smul
         (from-nnrat (inverse 'ap 'gp))
         (sadd left-envelope right-envelope))
        binders
        (into
         (tail-binders)
         [['threshold signed]
          ['tail-envelope-at-most-threshold
           (sle scaled-aggregate 'threshold)]])]
    {:name 'bellman/signed-policy-iterate-tail-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle (sup-distance left-at right-at) 'threshold))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-general-rate-iterate-tail-stopping-certificate [])
       'rows 'reward 'initial 'ap 'gp
       'step-shape 'reward-shape 'positive-rows 'bounded-sums
       'left-steps 'right-steps
       'threshold 'tail-envelope-at-most-threshold))}))

(def definition-specs [signed-policy-step-spec signed-policy-iterate-spec])
(def theorem-specs
  [signed-policy-step-reward-cancels-distance-spec
   signed-policy-step-general-rate-contraction-spec
   signed-policy-fixed-points-unique-spec
   signed-policy-fixed-point-residual-bound-spec
   signed-policy-fixed-point-stopping-certificate-spec
   signed-policy-iterate-error-exact-envelope-spec
   signed-policy-iterate-stopping-certificate-spec
   signed-policy-iterate-tail-bound-spec
   signed-policy-iterate-tail-stopping-certificate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-general-rate-uniqueness rainbow.math.linear.matrix.affine-general-rate-tail-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-bellman-signed-policy (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.bellman-signed-policy))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
