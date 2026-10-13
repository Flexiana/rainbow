(ns rainbow.math.linear.matrix.action-scale
  "Arbitrary signed-scalar vector scaling for native matrix algebra.

  A signed rational is represented by its nonnegative positive and negative
  components.  Its vector action is therefore the difference between those two
  native nonnegative vector scalings.  This is definitionally the pointwise
  signed product, while exposing enough existing linear algebra to derive dot
  homogeneity without an expensive nested List induction.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.composable-multiply :as bracketings]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-algebra]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.linear.vector.dot-scale :as dot-scale]
            [rainbow.math.linear.vector.dot-subtract :as dot-subtract]
            [rainbow.math.linear.vector.shape-add :as shape-add]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- same-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))

(def signed-scale-spec
  {:name 'vector/signed-scale :kind :definition :universes []
   :type (function/arrow signed vector-type vector-type)
   :value
   (function/lam
    [['factor signed] ['values vector-type]]
    (vector-subtract
     (vector-scale (positive 'factor) 'values)
     (vector-scale (negative 'factor) 'values)))})

(def multiply-distributes-add-left-spec
  {:name 'signed/multiply-distributes-add-left :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]]
    (signed-equivalent
     (signed-multiply 'factor (signed-add 'left 'right))
     (signed-add
      (signed-multiply 'factor 'left)
      (signed-multiply 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]]
    (let [start (signed-multiply 'factor (signed-add 'left 'right))
          commuted (signed-multiply (signed-add 'left 'right) 'factor)
          split
          (signed-add
           (signed-multiply 'left 'factor)
           (signed-multiply 'right 'factor))
          finish
          (signed-add
           (signed-multiply 'factor 'left)
           (signed-multiply 'factor 'right))]
      (transitive
       start split finish
       (transitive
        start commuted split
        (app (function/const* 'signed/multiply-commutative [])
             'factor (signed-add 'left 'right))
        (app
         (function/const* 'signed/multiply-distributes-add-right [])
         'left 'right 'factor))
       (app
        (function/const* 'signed/add-respects-equivalence [])
        (signed-multiply 'left 'factor)
        (signed-multiply 'factor 'left)
        (signed-multiply 'right 'factor)
        (signed-multiply 'factor 'right)
        (app (function/const* 'signed/multiply-commutative [])
             'left 'factor)
        (app (function/const* 'signed/multiply-commutative [])
             'right 'factor)))))})

(def scale-difference-multiply-spec
  {:name 'signed/scale-difference-multiply :universes []
   :type
   (function/forall
    [['factor signed] ['value signed]]
    (signed-equivalent
     (signed-subtract
      (scalar-scale (positive 'factor) 'value)
      (scalar-scale (negative 'factor) 'value))
     (signed-multiply 'factor 'value)))
   :value
   (function/lam
    [['factor signed] ['value signed]]
    (app (function/const* 'signed/equivalent-reflexive [])
         (signed-multiply 'factor 'value)))})

(def signed-scale-preserves-shape-spec
  {:name 'vector/signed-scale-preserves-shape :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type]]
    (same-shape (signed-scale 'factor 'values) 'values))
   :value
   (function/lam
    [['factor signed] ['values vector-type]]
    (let [positive-values (vector-scale (positive 'factor) 'values)
          negative-values (vector-scale (negative 'factor) 'values)
          positive-shape
          (app (function/const* 'vector/scale-preserves-shape [])
               (positive 'factor) 'values)
          negative-shape
          (app (function/const* 'vector/scale-preserves-shape [])
               (negative 'factor) 'values)
          scales-same
          (same-shape-transitive
           positive-values 'values negative-values
           positive-shape
           (same-shape-symmetric
            negative-values 'values negative-shape))
          difference-shapes
          (app (function/const* 'vector/subtract-preserves-shape [])
               positive-values negative-values scales-same)
          difference-positive
          (proposition-left
           (same-shape
            (vector-subtract positive-values negative-values)
            positive-values)
           (same-shape
            (vector-subtract positive-values negative-values)
            negative-values)
           difference-shapes)]
      (same-shape-transitive
       (signed-scale 'factor 'values) positive-values 'values
       difference-positive positive-shape)))})

(def dot-signed-scale-left-spec
  {:name 'vector/dot-signed-scale-left :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot (signed-scale 'factor 'values) 'weights)
     (signed-multiply 'factor (dot 'values 'weights))))
   :value
   (function/lam
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (let [positive-rate (positive 'factor)
          negative-rate (negative 'factor)
          positive-values (vector-scale positive-rate 'values)
          negative-values (vector-scale negative-rate 'values)
          values-dot (dot 'values 'weights)
          start (dot (signed-scale 'factor 'values) 'weights)
          split
          (signed-subtract
           (dot positive-values 'weights)
           (dot negative-values 'weights))
          scaled
          (signed-subtract
           (scalar-scale positive-rate values-dot)
           (scalar-scale negative-rate values-dot))
          finish (signed-multiply 'factor values-dot)
          positive-shape
          (app (function/const* 'vector/scale-preserves-shape [])
               positive-rate 'values)
          negative-shape
          (app (function/const* 'vector/scale-preserves-shape [])
               negative-rate 'values)
          scales-same
          (same-shape-transitive
           positive-values 'values negative-values
           positive-shape
           (same-shape-symmetric
            negative-values 'values negative-shape))]
      (transitive
       start scaled finish
       (transitive
        start split scaled
        (app (function/const* 'vector/dot-subtract-left [])
             positive-values negative-values 'weights scales-same)
        (app (function/const* 'signed/subtract-respects-equivalence [])
             (dot positive-values 'weights)
             (scalar-scale positive-rate values-dot)
             (dot negative-values 'weights)
             (scalar-scale negative-rate values-dot)
             (app (function/const* 'vector/dot-scale-left [])
                  positive-rate 'values 'weights)
             (app (function/const* 'vector/dot-scale-left [])
                  negative-rate 'values 'weights)))
       (app (function/const* 'signed/scale-difference-multiply [])
            'factor values-dot))))})

(def definition-specs [signed-scale-spec])
(def theorem-specs
  [multiply-distributes-add-left-spec
   scale-difference-multiply-spec
   signed-scale-preserves-shape-spec
   dot-signed-scale-left-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.vector.shape-add])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/multiply-commutative :signed-multiply-ring signed-ring/multiply-commutative-spec) (extend-spec-if-missing 'signed/multiply-distributes-add-right :signed-distributive distributive/multiply-distributes-add-right-spec) (extend-spec-if-missing 'signed/add-respects-equivalence :signed-map-sum-algebra signed-algebra/add-respects-equivalence-spec) (support/extend-with :finite-matrix-action-scale (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.action-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
