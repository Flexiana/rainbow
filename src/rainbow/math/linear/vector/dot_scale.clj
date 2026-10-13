(ns rainbow.math.linear.vector.dot-scale
  "Homogeneity of the native vector dot product in its first argument.

    signed/scale-zero
    signed/scale-multiply
    signed/scale-respects-equivalence
    vector/dot-scale-left
    vector/dot-scale-right

  The scalar laws are semiring identities checked through the verified nnrat
  ring normalizer.  Dot homogeneity is then one List induction, combining the
  scalar product law, the tail hypothesis, and signed scale additivity."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.scale-additive :as signed-additive]
            [rainbow.math.linear.vector.dot-bilinear :as bilinear]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(def scale-zero-spec
  {:name 'signed/scale-zero :universes []
   :type
   (function/forall
    [['rate nnrat]]
    (signed-equivalent (signed-scale 'rate signed-zero) signed-zero))
   :value
   (function/lam
    [['rate nnrat]]
    (let [scaled-zero (ring/rmul 'rate nnrat-zero)]
      (ring/equiv
       (ring/radd scaled-zero nnrat-zero)
       (ring/radd nnrat-zero scaled-zero))))})

(def scale-multiply-spec
  {:name 'signed/scale-multiply :universes []
   :type
   (function/forall
    [['rate nnrat] ['value signed] ['multiplier signed]]
    (signed-equivalent
     (signed-multiply (signed-scale 'rate 'value) 'multiplier)
     (signed-scale 'rate (signed-multiply 'value 'multiplier))))
   :value
   (function/lam
    [['rate nnrat] ['value signed] ['multiplier signed]]
    (let [value-positive (positive 'value)
          value-negative (negative 'value)
          multiplier-positive (positive 'multiplier)
          multiplier-negative (negative 'multiplier)
          left-positive
          (ring/radd
           (ring/rmul (ring/rmul 'rate value-positive)
                      multiplier-positive)
           (ring/rmul (ring/rmul 'rate value-negative)
                      multiplier-negative))
          left-negative
          (ring/radd
           (ring/rmul (ring/rmul 'rate value-positive)
                      multiplier-negative)
           (ring/rmul (ring/rmul 'rate value-negative)
                      multiplier-positive))
          right-positive
          (ring/rmul
           'rate
           (ring/radd (ring/rmul value-positive multiplier-positive)
                      (ring/rmul value-negative multiplier-negative)))
          right-negative
          (ring/rmul
           'rate
           (ring/radd (ring/rmul value-positive multiplier-negative)
                      (ring/rmul value-negative multiplier-positive)))]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def scale-respects-equivalence-spec
  {:name 'signed/scale-respects-equivalence :universes []
   :type
   (function/forall
    [['rate nnrat] ['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (signed-equivalent
     (signed-scale 'rate 'left)
     (signed-scale 'rate 'right)))
   :value
   (function/lam
    [['rate nnrat] ['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (let [source-left
          (ring/radd (positive 'left) (negative 'right))
          source-right
          (ring/radd (positive 'right) (negative 'left))
          scaled-source-left (ring/rmul 'rate source-left)
          scaled-source-right (ring/rmul 'rate source-right)
          goal-left
          (ring/radd (ring/rmul 'rate (positive 'left))
                     (ring/rmul 'rate (negative 'right)))
          goal-right
          (ring/radd (ring/rmul 'rate (positive 'right))
                     (ring/rmul 'rate (negative 'left)))
          scale-source
          (app (function/const* 'nnrat/multiply-respects-equivalence [])
               'rate 'rate source-left source-right
               (app (function/const* 'nnrat/equivalent-reflexive []) 'rate)
               'same)]
      (rat-transitive
       goal-left scaled-source-right goal-right
       (rat-transitive
        goal-left scaled-source-left scaled-source-right
        (ring/equiv goal-left scaled-source-left)
        scale-source)
       (ring/equiv scaled-source-right goal-right))))})

(def dot-scale-left-spec
  {:name 'vector/dot-scale-left :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot (vector-scale 'rate 'values) 'weights)
     (signed-scale 'rate (dot 'values 'weights))))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type] ['weights vector-type]]
    (let [zero-backward
          (symmetric
           (signed-scale 'rate signed-zero) signed-zero
           (app (function/const* 'signed/scale-zero []) 'rate))
          outer-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-weights vector-type]]
            (signed-equivalent
             (dot (vector-scale 'rate 'current-values) 'current-weights)
             (signed-scale
              'rate (dot 'current-values 'current-weights)))))
          outer-base
          (function/lam
           [['current-weights vector-type]]
           zero-backward)
          outer-step
          (function/lam
           [['value-head signed] ['value-tail vector-type]
            ['tail-homogeneous (app outer-motive 'value-tail)]]
           (let [current-values
                 (app (function/const* 'data/cons [type-level])
                      signed 'value-head 'value-tail)
                 weight-motive
                 (function/lam
                  [['current-weights vector-type]]
                  (signed-equivalent
                   (dot
                    (vector-scale 'rate current-values)
                    'current-weights)
                   (signed-scale
                    'rate (dot current-values 'current-weights))))]
             (function/lam
              [['current-weights vector-type]]
              (list-rec
               weight-motive
               zero-backward
               (function/lam
                [['weight-head signed] ['weight-tail vector-type]
                 ['ignored (app weight-motive 'weight-tail)]]
                (let [product
                      (signed-multiply 'value-head 'weight-head)
                      scaled-product
                      (signed-multiply
                       (signed-scale 'rate 'value-head)
                       'weight-head)
                      tail-dot (dot 'value-tail 'weight-tail)
                      scaled-tail-dot
                      (dot
                       (vector-scale 'rate 'value-tail)
                       'weight-tail)
                      start (signed-add scaled-product scaled-tail-dot)
                      middle
                      (signed-add
                       (signed-scale 'rate product)
                       (signed-scale 'rate tail-dot))
                      finish (signed-scale 'rate (signed-add product tail-dot))
                      split
                      (app
                       (function/const* 'signed/add-respects-equivalence [])
                       scaled-product (signed-scale 'rate product)
                       scaled-tail-dot (signed-scale 'rate tail-dot)
                       (app (function/const* 'signed/scale-multiply [])
                            'rate 'value-head 'weight-head)
                       (app 'tail-homogeneous 'weight-tail))
                      combine
                      (symmetric
                       finish middle
                       (app (function/const* 'signed/scale-additive [])
                            'rate product tail-dot))]
                  (transitive start middle finish split combine)))
               'current-weights))))]
      (app (list-rec outer-motive outer-base outer-step 'values)
           'weights)))})

(def dot-scale-right-spec
  {:name 'vector/dot-scale-right :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot 'values (vector-scale 'rate 'weights))
     (signed-scale 'rate (dot 'values 'weights))))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type] ['weights vector-type]]
    (let [scaled-weights (vector-scale 'rate 'weights)
          start (dot 'values scaled-weights)
          commuted (dot scaled-weights 'values)
          scaled-commuted (signed-scale 'rate (dot 'weights 'values))
          finish (signed-scale 'rate (dot 'values 'weights))]
      (transitive
       start scaled-commuted finish
       (transitive
        start commuted scaled-commuted
        (app (function/const* 'vector/dot-commutative [])
             'values scaled-weights)
        (app (function/const* 'vector/dot-scale-left [])
             'rate 'weights 'values))
       (app (function/const* 'signed/scale-respects-equivalence [])
            'rate (dot 'weights 'values) (dot 'values 'weights)
            (app (function/const* 'vector/dot-commutative [])
                 'weights 'values)))))})

(def definition-specs [])
(def theorem-specs
  [scale-zero-spec
   scale-multiply-spec
   scale-respects-equivalence-spec
   dot-scale-left-spec
   dot-scale-right-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.dot-bilinear])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/scale-additive :signed-scale-additive signed-additive/scale-additive-spec) (support/extend-with :vector-dot-scale theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.dot-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
