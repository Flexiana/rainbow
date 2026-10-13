(ns rainbow.math.linear.vector.norm-laws
  "Algebraic laws for the exact signed squared norm.

    norm/norm-squared-negate
    norm/norm-squared-scale

  Negating every component leaves the squared norm equivalent.  Scaling every
  component by a nonnegative rational rate scales the squared norm by
  rate*rate.  Both are theorem-only consequences of native dot bilinearity;
  they add no numerical square-root assumption."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.negate-additive :as signed-additive]
            [rainbow.math.rational.signed.order :as signed-order]
            [rainbow.math.rational.signed.scale-additive :as scale-additive]
            [rainbow.math.rational.signed.scale-composition :as composition]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.linear.vector.dot-scale :as dot-scale]
            [rainbow.math.linear.vector.norm :as norm]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nnrat-multiply [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def norm-squared-negate-spec
  {:name 'norm/norm-squared-negate :universes []
   :type
   (function/forall
    [['values vector-type]]
    (signed-equivalent
     (norm-squared (vector-negate 'values))
     (norm-squared 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [negated-values (vector-negate 'values)
          square (dot 'values 'values)
          start (dot negated-values negated-values)
          once-negated
          (signed-negate (dot 'values negated-values))
          twice-negated (signed-negate (signed-negate square))
          move-first-negation
          (app (function/const* 'vector/dot-negate-left [])
               'values negated-values)
          move-second-negation
          (app (function/const* 'signed/negate-respects-equivalence [])
               (dot 'values negated-values)
               (signed-negate square)
               (app (function/const* 'vector/dot-negate-right [])
                    'values 'values))]
      (transitive
       start twice-negated square
       (transitive
        start once-negated twice-negated
        move-first-negation move-second-negation)
       (app (function/const* 'signed/negate-involutive []) square))))})

(def norm-squared-scale-spec
  {:name 'norm/norm-squared-scale :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type]]
    (signed-equivalent
     (norm-squared (vector-scale 'rate 'values))
     (signed-scale
      (nnrat-multiply 'rate 'rate)
      (norm-squared 'values))))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type]]
    (let [scaled-values (vector-scale 'rate 'values)
          square (dot 'values 'values)
          start (dot scaled-values scaled-values)
          scaled-once
          (signed-scale 'rate (dot 'values scaled-values))
          scaled-twice
          (signed-scale 'rate (signed-scale 'rate square))
          finish
          (signed-scale (nnrat-multiply 'rate 'rate) square)
          move-left-scale
          (app (function/const* 'vector/dot-scale-left [])
               'rate 'values scaled-values)
          move-right-scale
          (app (function/const* 'signed/scale-respects-equivalence [])
               'rate
               (dot 'values scaled-values)
               (signed-scale 'rate square)
               (app (function/const* 'vector/dot-scale-right [])
                    'rate 'values 'values))]
      (transitive
       start scaled-twice finish
       (transitive
        start scaled-once scaled-twice
        move-left-scale move-right-scale)
       (app (function/const* 'signed/scale-composition [])
            'rate 'rate square))))})

(def definition-specs [])
(def theorem-specs
  [norm-squared-negate-spec norm-squared-scale-spec])

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
  '[rainbow.math.linear.vector.dot-negate])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/scale-additive :signed-scale-additive scale-additive/scale-additive-spec) (extend-specs-if-missing :vector-dot-scale dot-scale/theorem-specs) norm/extend-environment (extend-spec-if-missing 'signed/scale-composition :signed-scale-composition composition/scale-composition-spec) (extend-spec-if-missing 'signed/negate-involutive :signed-order signed-order/negate-involutive-spec) (support/extend-with :vector-norm-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.norm-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
