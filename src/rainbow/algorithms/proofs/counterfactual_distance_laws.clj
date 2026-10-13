(ns rainbow.algorithms.proofs.counterfactual-distance-laws
  "Native algebraic laws for exact counterfactual squared distance.

    counterfactual/distance-squared-symmetric
    counterfactual/distance-squared-self-zero
    counterfactual/distance-squared-zero-of-equivalent

  Symmetry transports norm invariance under negation across
  `-(left - right) ~ right - left`.  Self-distance and equivalence use the
  shape-preserving zero vector and squared-norm congruence.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.counterfactual-distance-separation :as separation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.equivalence-laws :as signed-equivalence]
            [rainbow.math.rational.signed.limit-uniqueness :as signed-antisymmetry]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-add]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.rational.signed.negate-additive :as signed-additive]
            [rainbow.math.rational.signed.order-monotone :as signed-monotone]
            [rainbow.math.rational.signed.order-transitivity :as signed-transitivity]
            [rainbow.math.rational.signed.unit-laws :as signed-units]
            [rainbow.math.rational.signed.rational :as signed-rational]
            [rainbow.math.linear.vector.add-order :as add-order]
            [rainbow.math.linear.vector.additive-units :as units]
            [rainbow.math.linear.vector.dot-commutative :as dot-commutative]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.linear.vector.dot-zero-laws :as zero-laws]
            [rainbow.math.linear.vector.equivalence-laws :as equivalence-laws]
            [rainbow.math.linear.vector.equivalence-transitivity :as transitivity]
            [rainbow.math.linear.vector.negate-additive :as negate-additive]
            [rainbow.math.linear.vector.norm-congruence :as congruence]
            [rainbow.math.linear.vector.norm-laws :as norm-laws]
            [rainbow.math.linear.vector.pointwise-order :as pointwise]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]
            [rainbow.math.linear.vector.subtract-laws :as subtract-laws]
            [rainbow.math.linear.vector.subtract-negation :as subtract-negation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- distance-squared [left right]
  (app (function/const* 'counterfactual/distance-squared []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(def distance-squared-symmetric-spec
  {:name 'counterfactual/distance-squared-symmetric :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (signed-equivalent
     (distance-squared 'left 'right)
     (distance-squared 'right 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [forward (vector-subtract 'left 'right)
          reverse (vector-subtract 'right 'left)
          negated-forward (vector-negate forward)
          forward-square (norm-squared forward)
          negated-square (norm-squared negated-forward)
          reverse-square (norm-squared reverse)]
      (transitive
       forward-square negated-square reverse-square
       (symmetric
        negated-square forward-square
        (app (function/const* 'norm/norm-squared-negate []) forward))
       (app
        (function/const* 'norm/norm-squared-respects-equivalence [])
        negated-forward reverse
        (app (function/const* 'vector/negate-subtract [])
             'left 'right)))))})

(def distance-squared-self-zero-spec
  {:name 'counterfactual/distance-squared-self-zero :universes []
   :type
   (function/forall
    [['values vector-type]]
    (signed-equivalent
     (distance-squared 'values 'values) signed-zero))
   :value
   (function/lam
    [['values vector-type]]
    (let [difference (vector-subtract 'values 'values)
          zeros (zero-like 'values)]
      (transitive
       (norm-squared difference) (norm-squared zeros) signed-zero
       (app
        (function/const* 'norm/norm-squared-respects-equivalence [])
        difference zeros
        (app
         (function/const*
          'vector/subtract-self-equivalent-zero-like [])
         'values))
       (app (function/const* 'norm/norm-squared-zero-like [])
            'values))))})

(def distance-squared-zero-of-equivalent-spec
  {:name 'counterfactual/distance-squared-zero-of-equivalent :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (signed-equivalent
     (distance-squared 'left 'right) signed-zero))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [difference (vector-subtract 'left 'right)
          self-difference (vector-subtract 'left 'left)
          differences-same
          (app
           (function/const* 'vector/subtract-respects-equivalence [])
           'left 'left 'right 'left
           (app (function/const* 'vector/equivalent-reflexive []) 'left)
           (app (function/const* 'vector/equivalent-symmetric [])
                'left 'right 'same))]
      (transitive
       (norm-squared difference) (norm-squared self-difference) signed-zero
       (app
        (function/const* 'norm/norm-squared-respects-equivalence [])
        difference self-difference differences-same)
       (app
        (function/const* 'counterfactual/distance-squared-self-zero [])
        'left))))})

(def definition-specs [])
(def theorem-specs
  [distance-squared-symmetric-spec
   distance-squared-self-zero-spec
   distance-squared-zero-of-equivalent-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   checked-environment
   specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.counterfactual-distance-separation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/equivalent-reflexive :signed-rational signed-rational/equivalent-reflexive-spec) (extend-spec-if-missing 'signed/negate-additive :signed-negate-additive signed-additive/negate-additive-spec) (extend-spec-if-missing 'signed/at-most-transitive :signed-order-transitivity signed-transitivity/at-most-transitive-spec) (extend-spec-if-missing 'signed/at-most-antisymmetric :signed-limit-uniqueness signed-antisymmetry/signed-at-most-antisymmetric-spec) (extend-spec-if-missing 'signed/equivalent-symmetric :signed-equivalence-laws signed-equivalence/equivalent-symmetric-spec) (extend-spec-if-missing 'signed/negate-respects-equivalence :signed-equivalence-laws signed-equivalence/negate-respects-equivalence-spec) (extend-spec-if-missing 'signed/equivalent-to-at-most :signed-unit-laws signed-units/equivalent-to-at-most-spec) (extend-specs-if-missing :signed-order-monotone signed-monotone/theorem-specs) (extend-spec-if-missing 'signed/add-commutative :nnrat-commutative commutative/signed-add-commutative-spec) (extend-spec-if-missing 'signed/add-respects-equivalence :signed-map-sum-algebra signed-add/add-respects-equivalence-spec) (extend-specs-if-missing :signed-multiply-ring signed-ring/theorem-specs) (extend-spec-if-missing 'signed/multiply-zero-left :signed-distributive distributive/multiply-zero-left-spec) (extend-spec-if-missing 'vector/at-most :vector-pointwise-order pointwise/vector-at-most-spec) (extend-spec-if-missing 'vector/at-most-transitive :vector-pointwise-order-laws order-laws/at-most-transitive-spec) (extend-spec-if-missing 'vector/at-most-antisymmetric :vector-pointwise-order-laws order-laws/at-most-antisymmetric-spec) (extend-spec-if-missing 'vector/equivalent-to-mutual-at-most :vector-pointwise-order-laws order-laws/equivalent-to-mutual-at-most-spec) (extend-spec-if-missing 'vector/equivalent-transitive :vector-equivalence-transitivity transitivity/equivalent-transitive-spec) (extend-spec-if-missing 'vector/equivalent-reflexive :vector-equivalence-laws equivalence-laws/equivalent-reflexive-spec) (extend-spec-if-missing 'vector/equivalent-symmetric :vector-equivalence-laws equivalence-laws/equivalent-symmetric-spec) (extend-spec-if-missing 'vector/map-respects-equivalence :vector-equivalence-laws equivalence-laws/map-respects-equivalence-spec) (extend-spec-if-missing 'vector/negate-respects-equivalence :vector-equivalence-laws equivalence-laws/negate-respects-equivalence-spec) (extend-spec-if-missing 'vector/negate-involutive :vector-equivalence-laws equivalence-laws/negate-involutive-spec) (extend-specs-if-missing :vector-add-order [add-order/add-right-monotone-spec add-order/add-left-monotone-spec add-order/add-monotone-spec add-order/add-respects-equivalence-spec add-order/add-commutative-spec]) (extend-spec-if-missing 'vector/negate-additive :vector-negate-additive negate-additive/negate-additive-spec) (extend-spec-if-missing 'vector/negate-subtract :vector-subtract-negation subtract-negation/negate-subtract-spec) (extend-spec-if-missing 'vector/dot-commutative :vector-dot-commutative dot-commutative/dot-commutative-spec) (extend-specs-if-missing :vector-dot-negate dot-negate/theorem-specs) (extend-spec-if-missing 'norm/norm-squared-negate :vector-norm-laws norm-laws/norm-squared-negate-spec) (extend-spec-if-missing 'norm/norm-squared-respects-equivalence :vector-norm-congruence congruence/norm-squared-respects-equivalence-spec) (extend-spec-if-missing 'signed/subtract-self-equivalent-zero :signed-unit-laws signed-units/subtract-self-equivalent-zero-spec) (extend-spec-if-missing 'vector/subtract-self-equivalent-zero-like :vector-additive-units units/subtract-self-equivalent-zero-like-spec) (extend-spec-if-missing 'vector/dot-zero-like-left :vector-dot-zero-laws zero-laws/dot-zero-like-left-spec) (extend-spec-if-missing 'norm/norm-squared-zero-like :vector-dot-zero-laws zero-laws/norm-squared-zero-like-spec) (extend-spec-if-missing 'vector/subtract-respects-equivalence :vector-subtract-laws subtract-laws/subtract-respects-equivalence-spec) (support/extend-with :counterfactual-distance-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.counterfactual-distance-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
