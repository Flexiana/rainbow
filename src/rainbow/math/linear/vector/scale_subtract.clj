(ns rainbow.math.linear.vector.scale-subtract
  "Uniform nonnegative scaling commutes with negation and subtraction.

    scale rate (-values)       ~  -(scale rate values)
    scale rate (left - right)  ~  scale rate left - scale rate right

  At each scalar head, scaling a negated Grothendieck pair and negating a scaled
  pair are definitionally the same pair.  Subtraction distribution then composes
  this result with vector/scale-additive.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassoc]
            [rainbow.math.rational.nnrat.distribute-right :as distribute]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.product-reassociation :as product-reassoc]
            [rainbow.math.rational.signed.scale-additive :as signed-additive]
            [rainbow.math.linear.vector.add-reorder :as add-reorder]
            [rainbow.math.linear.vector.scale-additive :as scale-additive]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- reflexive [values]
  (app (function/const* 'vector/equivalent-reflexive []) values))

(def trivial (function/const* 'proposition/trivial []))

(def scale-negate-spec
  {:name 'vector/scale-negate :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type]]
    (vector-equivalent
     (vector-scale 'rate (vector-negate 'values))
     (vector-negate (vector-scale 'rate 'values))))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-scale 'rate (vector-negate 'current))
            (vector-negate (vector-scale 'rate 'current))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-commutes (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-scale 'rate (signed-negate 'head))
             (signed-negate (signed-scale 'rate 'head)))
            (vector-equivalent
             (vector-scale 'rate (vector-negate 'tail))
             (vector-negate (vector-scale 'rate 'tail)))
            (app (function/const* 'signed/equivalent-reflexive [])
                 (signed-scale 'rate (signed-negate 'head)))
            'tail-commutes))]
      (list-rec motive trivial step 'values)))})

(def scale-subtract-spec
  {:name 'vector/scale-subtract :universes []
   :type
   (function/forall
    [['rate nnrat] ['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-scale 'rate (vector-subtract 'left 'right))
     (vector-subtract
      (vector-scale 'rate 'left)
      (vector-scale 'rate 'right))))
   :value
   (function/lam
    [['rate nnrat] ['left vector-type] ['right vector-type]]
    (let [negated-right (vector-negate 'right)
          scaled-left (vector-scale 'rate 'left)
          scaled-negated (vector-scale 'rate negated-right)
          negated-scaled (vector-negate (vector-scale 'rate 'right))
          start (vector-scale 'rate (vector-subtract 'left 'right))
          distributed (vector-add scaled-left scaled-negated)
          finish (vector-subtract scaled-left (vector-scale 'rate 'right))
          distribute
          (app (function/const* 'vector/scale-additive [])
               'rate 'left negated-right)
          commute-negation
          (app (function/const* 'vector/add-respects-equivalence [])
               scaled-left scaled-left
               scaled-negated negated-scaled
               (reflexive scaled-left)
               (app (function/const* 'vector/scale-negate [])
                    'rate 'right))]
      (transitive
       start distributed finish distribute commute-negation)))})

(def definition-specs [])
(def theorem-specs [scale-negate-spec scale-subtract-spec])

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
  '[rainbow.math.linear.vector.add-reorder])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-specs-if-missing :nnrat-add-monotone add-monotone/theorem-specs) (extend-specs-if-missing :nnrat-multiply-commute multiply-commute/theorem-specs) (extend-specs-if-missing :nnrat-product-reassociation product-reassoc/theorem-specs) (extend-specs-if-missing :nnrat-additive-reassociation add-reassoc/theorem-specs) (extend-specs-if-missing :nnrat-distribute-right distribute/theorem-specs) (extend-spec-if-missing 'signed/scale-additive :signed-scale-additive signed-additive/scale-additive-spec) (extend-spec-if-missing 'vector/scale-additive :vector-scale-additive scale-additive/scale-additive-spec) (support/extend-with :vector-scale-subtract theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.scale-subtract))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
