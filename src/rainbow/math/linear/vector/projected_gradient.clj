(ns rainbow.math.linear.vector.projected-gradient
  "Projected-gradient steps on finite signed-rational vectors.

    projected-step lo hi rate point gradient
      = uniform-clamp lo hi (point - rate * gradient)

  This composes Rainbow's native vector arithmetic with the signed box
  projection.  Every step is componentwise feasible for an ordered interval;
  projecting it again is idempotent up to vector equivalence; and projection
  preserves any componentwise order already established between two raw
  updates.  These are n-dimensional theorems, not scalar projection aliases.
  Native and axiom-free on D63."
  (:require [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- raw-update [rate point gradient]
  (vector-subtract point (vector-scale rate gradient)))
(defn- uniform-clamp [lower upper values]
  (app (function/const* 'vector/uniform-clamp []) lower upper values))
(defn- projected-step [lower upper rate point gradient]
  (app (function/const* 'optimization/vector-projected-step [])
       lower upper rate point gradient))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- in-band [lower upper values]
  (app (function/const* 'vector/in-band []) lower upper values))
(defn- eq-vector [left right]
  (function/equality type-level vector-type left right))
(defn- reflexive-vector [value]
  (app (function/const* 'equality/reflexive [type-level])
       vector-type value))

(def projected-step-spec
  {:name 'optimization/vector-projected-step
   :kind :definition :universes []
   :transparency :reducible
   :type
   (function/arrow signed signed nnrat vector-type vector-type vector-type)
   :value
   (function/lam
    [['lower signed] ['upper signed] ['rate nnrat]
     ['point vector-type] ['gradient vector-type]]
    (uniform-clamp
     'lower 'upper (raw-update 'rate 'point 'gradient)))})

(def projected-step-unfold-spec
  {:name 'optimization/vector-projected-step-unfold :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['rate nnrat]
     ['point vector-type] ['gradient vector-type]]
    (eq-vector
     (projected-step 'lower 'upper 'rate 'point 'gradient)
     (uniform-clamp
      'lower 'upper (raw-update 'rate 'point 'gradient))))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['rate nnrat]
     ['point vector-type] ['gradient vector-type]]
    (reflexive-vector
     (projected-step 'lower 'upper 'rate 'point 'gradient)))})

(def projected-step-in-band-spec
  {:name 'optimization/vector-projected-step-in-band :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['rate nnrat] ['point vector-type] ['gradient vector-type]]
    (in-band
     'lower 'upper
     (projected-step 'lower 'upper 'rate 'point 'gradient)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['rate nnrat] ['point vector-type] ['gradient vector-type]]
    (app (function/const* 'vector/uniform-clamp-in-band [])
         'lower 'upper 'ordered
         (raw-update 'rate 'point 'gradient)))})

(def projected-step-reprojection-spec
  {:name 'optimization/vector-projected-step-reprojection :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['rate nnrat] ['point vector-type] ['gradient vector-type]]
    (vector-equivalent
     (uniform-clamp
      'lower 'upper
      (projected-step 'lower 'upper 'rate 'point 'gradient))
     (projected-step 'lower 'upper 'rate 'point 'gradient)))
   :value
   (function/lam
    [['lower signed] ['upper signed]
     ['ordered (at-most 'lower 'upper)]
     ['rate nnrat] ['point vector-type] ['gradient vector-type]]
    (app (function/const* 'vector/uniform-clamp-idempotent [])
         'lower 'upper 'ordered
         (raw-update 'rate 'point 'gradient)))})

(def projected-step-monotone-spec
  {:name 'optimization/vector-projected-step-monotone :universes []
   :type
   (function/forall
    [['lower signed] ['upper signed] ['rate nnrat]
     ['left-point vector-type] ['left-gradient vector-type]
     ['right-point vector-type] ['right-gradient vector-type]
     ['raw-ordered
      (vector-at-most
       (raw-update 'rate 'left-point 'left-gradient)
       (raw-update 'rate 'right-point 'right-gradient))]]
    (vector-at-most
     (projected-step
      'lower 'upper 'rate 'left-point 'left-gradient)
     (projected-step
      'lower 'upper 'rate 'right-point 'right-gradient)))
   :value
   (function/lam
    [['lower signed] ['upper signed] ['rate nnrat]
     ['left-point vector-type] ['left-gradient vector-type]
     ['right-point vector-type] ['right-gradient vector-type]
     ['raw-ordered
      (vector-at-most
       (raw-update 'rate 'left-point 'left-gradient)
       (raw-update 'rate 'right-point 'right-gradient))]]
    (app (function/const* 'vector/uniform-clamp-monotone [])
         'lower 'upper
         (raw-update 'rate 'left-point 'left-gradient)
         (raw-update 'rate 'right-point 'right-gradient)
         'raw-ordered))})

(def definition-specs [projected-step-spec])
(def theorem-specs
  [projected-step-unfold-spec
   projected-step-in-band-spec
   projected-step-reprojection-spec
   projected-step-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      finite-vector/extend-environment
      order-laws/extend-environment
      (support/extend-with :vector-projected-gradient
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
