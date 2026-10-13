(ns rainbow.algorithms.proofs.counterfactual-objective-laws
  "Native guarantees for the exact counterfactual optimization objective.

    counterfactual/objective
      = distance-squared + scale(weight, class-penalty)

    signed/scale-nonnegative
    counterfactual/objective-nonnegative
    counterfactual/distance-squared-at-most-objective
    counterfactual/equivalent-of-objective-zero

  A nonnegative-rational weight preserves a nonnegative signed penalty.  Hence
  the objective is nonnegative, cannot undercut its proximity term, and—under
  the necessary same-shape hypothesis—can be zero only for equivalent plans.
  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.counterfactual-distance-laws :as distance-laws]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.signed.scale-order :as scale-order]
            [rainbow.math.temporal-difference :as temporal-difference]
            [rainbow.math.linear.vector.dot-scale :as dot-scale]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- nonnegative [value]
  (app (function/const* 'signed/nonnegative []) value))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- distance-squared [left right]
  (app (function/const* 'counterfactual/distance-squared []) left right))
(defn- objective [original candidate weight class-penalty]
  (app (function/const* 'counterfactual/objective [])
       original candidate weight class-penalty))

(def objective-spec
  {:name 'counterfactual/objective :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type nnrat signed signed)
   :value
   (function/lam
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]]
    (signed-add
     (distance-squared 'original 'candidate)
     (signed-scale 'weight 'class-penalty)))})

(def scale-nonnegative-spec
  {:name 'signed/scale-nonnegative :universes []
   :type
   (function/forall
    [['rate nnrat] ['value signed]
     ['value-nonnegative (nonnegative 'value)]]
    (nonnegative (signed-scale 'rate 'value)))
   :value
   (function/lam
    [['rate nnrat] ['value signed]
     ['value-nonnegative (nonnegative 'value)]]
    (let [scaled-zero (signed-scale 'rate signed-zero)
          scaled-value (signed-scale 'rate 'value)
          zero-at-most-value
          (app (function/const* 'signed/zero-at-most-of-nonnegative [])
               'value 'value-nonnegative)
          scaled-order
          (app (function/const* 'signed/scale-monotone [])
               'rate signed-zero 'value zero-at-most-value)
          zero-at-most-scaled
          (app
           (function/const* 'signed/at-most-respects-equivalence [])
           scaled-zero signed-zero scaled-value scaled-value
           (app (function/const* 'signed/scale-zero []) 'rate)
           (app (function/const* 'signed/equivalent-reflexive [])
                scaled-value)
           scaled-order)]
      (app (function/const* 'signed/nonnegative-of-zero-at-most [])
           scaled-value zero-at-most-scaled)))})

(def objective-nonnegative-spec
  {:name 'counterfactual/objective-nonnegative :universes []
   :type
   (function/forall
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['penalty-nonnegative (nonnegative 'class-penalty)]]
    (nonnegative
     (objective 'original 'candidate 'weight 'class-penalty)))
   :value
   (function/lam
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['penalty-nonnegative (nonnegative 'class-penalty)]]
    (app
     (function/const* 'signed/add-nonnegative [])
     (distance-squared 'original 'candidate)
     (signed-scale 'weight 'class-penalty)
     (app
      (function/const* 'counterfactual/distance-squared-nonnegative [])
      'original 'candidate)
     (app (function/const* 'signed/scale-nonnegative [])
          'weight 'class-penalty 'penalty-nonnegative)))})

(def distance-squared-at-most-objective-spec
  {:name 'counterfactual/distance-squared-at-most-objective :universes []
   :type
   (function/forall
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['penalty-nonnegative (nonnegative 'class-penalty)]]
    (signed-at-most
     (distance-squared 'original 'candidate)
     (objective 'original 'candidate 'weight 'class-penalty)))
   :value
   (function/lam
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['penalty-nonnegative (nonnegative 'class-penalty)]]
    (let [distance (distance-squared 'original 'candidate)
          scaled-penalty (signed-scale 'weight 'class-penalty)
          padded-distance (signed-add distance signed-zero)
          full-objective (signed-add distance scaled-penalty)
          scaled-nonnegative
          (app (function/const* 'signed/scale-nonnegative [])
               'weight 'class-penalty 'penalty-nonnegative)
          zero-at-most-scaled
          (app (function/const* 'signed/zero-at-most-of-nonnegative [])
               scaled-penalty scaled-nonnegative)]
      (app
       (function/const* 'signed/at-most-respects-equivalence [])
       padded-distance distance full-objective full-objective
       (app (function/const* 'signed/add-zero-right []) distance)
       (app (function/const* 'signed/equivalent-reflexive [])
            full-objective)
       (app (function/const* 'signed/add-left-monotone [])
            signed-zero scaled-penalty distance zero-at-most-scaled))))})

(def equivalent-of-objective-zero-spec
  {:name 'counterfactual/equivalent-of-objective-zero :universes []
   :type
   (function/forall
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['shape (same-shape 'original 'candidate)]
     ['penalty-nonnegative (nonnegative 'class-penalty)]
     ['objective-zero
      (signed-equivalent
       (objective 'original 'candidate 'weight 'class-penalty)
       signed-zero)]]
    (vector-equivalent 'original 'candidate))
   :value
   (function/lam
    [['original vector-type] ['candidate vector-type]
     ['weight nnrat] ['class-penalty signed]
     ['shape (same-shape 'original 'candidate)]
     ['penalty-nonnegative (nonnegative 'class-penalty)]
     ['objective-zero
      (signed-equivalent
       (objective 'original 'candidate 'weight 'class-penalty)
       signed-zero)]]
    (let [distance (distance-squared 'original 'candidate)
          scaled-penalty (signed-scale 'weight 'class-penalty)
          distance-nonnegative
          (app
           (function/const*
            'counterfactual/distance-squared-nonnegative [])
           'original 'candidate)
          scaled-nonnegative
          (app (function/const* 'signed/scale-nonnegative [])
               'weight 'class-penalty 'penalty-nonnegative)
          distance-zero
          (app
           (function/const*
            'signed/add-zero-split-nonnegative-left [])
           distance scaled-penalty
           distance-nonnegative scaled-nonnegative 'objective-zero)]
      (app
       (function/const*
        'counterfactual/equivalent-of-distance-squared-zero [])
       'original 'candidate 'shape distance-zero)))})

(def definition-specs [objective-spec])
(def theorem-specs
  [scale-nonnegative-spec
   objective-nonnegative-spec
   distance-squared-at-most-objective-spec
   equivalent-of-objective-zero-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.counterfactual-distance-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/scale :temporal-difference temporal-difference/scale-spec) (extend-spec-if-missing 'signed/scale-zero :vector-dot-scale dot-scale/scale-zero-spec) (extend-spec-if-missing 'signed/scale-monotone :signed-scale-order scale-order/scale-monotone-spec) (extend-spec-if-missing 'signed/at-most-respects-equivalence :signed-order-respects order-respects/at-most-respects-equivalence-spec) (support/extend-with :counterfactual-objective-laws (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.counterfactual-objective-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
