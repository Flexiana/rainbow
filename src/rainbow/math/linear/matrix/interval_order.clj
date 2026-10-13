(ns rainbow.math.linear.matrix.interval-order
  "Interval propagation for signed vectors and native finite matrices.

  Monotone and antitone dot, action, and product maps send an explicit
  pointwise interval to the corresponding endpoint interval.  Nonnegative
  fixed operands preserve endpoint orientation; nonpositive fixed operands
  reverse it.  These paired bounds are reusable certificates for Bellman
  enclosures and bounded OR trajectories.  Theorem-only and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.antitone :as antitone]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- dot [a b] (app (function/const* 'vector/dot []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- both [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))

(def dot-bounds-nonnegative-weights-spec
  {:name 'vector/dot-bounds-nonnegative-weights :universes []
   :type
   (function/forall
    [['lower vector-type] ['value vector-type] ['upper vector-type]
     ['weights vector-type]
     ['weights-positive (vle (vz 'weights) 'weights)]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (both (sle (dot 'lower 'weights) (dot 'value 'weights))
          (sle (dot 'value 'weights) (dot 'upper 'weights))))
   :value
   (function/lam
    [['lower vector-type] ['value vector-type] ['upper vector-type]
     ['weights vector-type]
     ['weights-positive (vle (vz 'weights) 'weights)]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (conjp
     (sle (dot 'lower 'weights) (dot 'value 'weights))
     (sle (dot 'value 'weights) (dot 'upper 'weights))
     (app (function/const* 'vector/dot-left-monotone [])
          'lower 'value 'weights 'lower-ordered 'weights-positive)
     (app (function/const* 'vector/dot-left-monotone [])
          'value 'upper 'weights 'upper-ordered 'weights-positive)))})

(def dot-bounds-nonpositive-weights-spec
  {:name 'vector/dot-bounds-nonpositive-weights :universes []
   :type
   (function/forall
    [['lower vector-type] ['value vector-type] ['upper vector-type]
     ['weights vector-type]
     ['weights-negative (vle 'weights (vz 'weights))]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (both (sle (dot 'upper 'weights) (dot 'value 'weights))
          (sle (dot 'value 'weights) (dot 'lower 'weights))))
   :value
   (function/lam
    [['lower vector-type] ['value vector-type] ['upper vector-type]
     ['weights vector-type]
     ['weights-negative (vle 'weights (vz 'weights))]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (conjp
     (sle (dot 'upper 'weights) (dot 'value 'weights))
     (sle (dot 'value 'weights) (dot 'lower 'weights))
     (app (function/const* 'vector/dot-left-antitone [])
          'value 'upper 'weights 'upper-ordered 'weights-negative)
     (app (function/const* 'vector/dot-left-antitone [])
          'lower 'value 'weights 'lower-ordered 'weights-negative)))})

(def action-bounds-nonnegative-rows-spec
  {:name 'matrix/vector-multiply-bounds-nonnegative-rows :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (both (vle (action 'rows 'lower) (action 'rows 'value))
          (vle (action 'rows 'value) (action 'rows 'upper))))
   :value
   (function/lam
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (conjp
     (vle (action 'rows 'lower) (action 'rows 'value))
     (vle (action 'rows 'value) (action 'rows 'upper))
     (app (function/const* 'matrix/vector-multiply-monotone-values [])
          'rows 'lower 'value 'rows-positive 'lower-ordered)
     (app (function/const* 'matrix/vector-multiply-monotone-values [])
          'rows 'value 'upper 'rows-positive 'upper-ordered)))})

(def action-bounds-nonpositive-rows-spec
  {:name 'matrix/vector-multiply-bounds-nonpositive-rows :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (both (vle (action 'rows 'upper) (action 'rows 'value))
          (vle (action 'rows 'value) (action 'rows 'lower))))
   :value
   (function/lam
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (conjp
     (vle (action 'rows 'upper) (action 'rows 'value))
     (vle (action 'rows 'value) (action 'rows 'lower))
     (app (function/const* 'matrix/vector-multiply-antitone-values [])
          'rows 'value 'upper 'rows-negative 'upper-ordered)
     (app (function/const* 'matrix/vector-multiply-antitone-values [])
          'rows 'lower 'value 'rows-negative 'lower-ordered)))})

(def action-bounds-nonnegative-values-spec
  {:name 'matrix/vector-multiply-bounds-nonnegative-values :universes []
   :type
   (function/forall
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['values vector-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (vle (action 'lower 'values) (action 'value 'values))
          (vle (action 'value 'values) (action 'upper 'values))))
   :value
   (function/lam
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['values vector-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (vle (action 'lower 'values) (action 'value 'values))
     (vle (action 'value 'values) (action 'upper 'values))
     (app (function/const* 'matrix/vector-multiply-monotone-rows [])
          'lower 'value 'values 'lower-ordered 'values-positive)
     (app (function/const* 'matrix/vector-multiply-monotone-rows [])
          'value 'upper 'values 'upper-ordered 'values-positive)))})

(def action-bounds-nonpositive-values-spec
  {:name 'matrix/vector-multiply-bounds-nonpositive-values :universes []
   :type
   (function/forall
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['values vector-type]
     ['values-negative (vle 'values (vz 'values))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (vle (action 'upper 'values) (action 'value 'values))
          (vle (action 'value 'values) (action 'lower 'values))))
   :value
   (function/lam
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['values vector-type]
     ['values-negative (vle 'values (vz 'values))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (vle (action 'upper 'values) (action 'value 'values))
     (vle (action 'value 'values) (action 'lower 'values))
     (app (function/const* 'matrix/vector-multiply-antitone-rows [])
          'value 'upper 'values 'upper-ordered 'values-negative)
     (app (function/const* 'matrix/vector-multiply-antitone-rows [])
          'lower 'value 'values 'lower-ordered 'values-negative)))})

(def multiply-bounds-left-nonnegative-factor-spec
  {:name 'matrix/multiply-bounds-left-nonnegative-factor :universes []
   :type
   (function/forall
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (mle (multiply 'lower 'factor) (multiply 'value 'factor))
          (mle (multiply 'value 'factor) (multiply 'upper 'factor))))
   :value
   (function/lam
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (mle (multiply 'lower 'factor) (multiply 'value 'factor))
     (mle (multiply 'value 'factor) (multiply 'upper 'factor))
     (app (function/const* 'matrix/multiply-monotone-left [])
          'lower 'value 'factor 'factor-positive 'lower-ordered)
     (app (function/const* 'matrix/multiply-monotone-left [])
          'value 'upper 'factor 'factor-positive 'upper-ordered)))})

(def multiply-bounds-left-nonpositive-factor-spec
  {:name 'matrix/multiply-bounds-left-nonpositive-factor :universes []
   :type
   (function/forall
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (mle (multiply 'upper 'factor) (multiply 'value 'factor))
          (mle (multiply 'value 'factor) (multiply 'lower 'factor))))
   :value
   (function/lam
    [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (mle (multiply 'upper 'factor) (multiply 'value 'factor))
     (mle (multiply 'value 'factor) (multiply 'lower 'factor))
     (app (function/const* 'matrix/multiply-antitone-left [])
          'value 'upper 'factor 'factor-negative 'upper-ordered)
     (app (function/const* 'matrix/multiply-antitone-left [])
          'lower 'value 'factor 'factor-negative 'lower-ordered)))})

(def multiply-bounds-right-nonnegative-factor-spec
  {:name 'matrix/multiply-bounds-right-nonnegative-factor :universes []
   :type
   (function/forall
    [['factor matrix-type]
     ['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (mle (multiply 'factor 'lower) (multiply 'factor 'value))
          (mle (multiply 'factor 'value) (multiply 'factor 'upper))))
   :value
   (function/lam
    [['factor matrix-type]
     ['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor-positive (mle (mz 'factor) 'factor)]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (mle (multiply 'factor 'lower) (multiply 'factor 'value))
     (mle (multiply 'factor 'value) (multiply 'factor 'upper))
     (app (function/const* 'matrix/multiply-monotone-right [])
          'factor 'lower 'value 'factor-positive 'lower-ordered)
     (app (function/const* 'matrix/multiply-monotone-right [])
          'factor 'value 'upper 'factor-positive 'upper-ordered)))})

(def multiply-bounds-right-nonpositive-factor-spec
  {:name 'matrix/multiply-bounds-right-nonpositive-factor :universes []
   :type
   (function/forall
    [['factor matrix-type]
     ['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (both (mle (multiply 'factor 'upper) (multiply 'factor 'value))
          (mle (multiply 'factor 'value) (multiply 'factor 'lower))))
   :value
   (function/lam
    [['factor matrix-type]
     ['lower matrix-type] ['value matrix-type] ['upper matrix-type]
     ['factor-negative (mle 'factor (mz 'factor))]
     ['lower-ordered (mle 'lower 'value)]
     ['upper-ordered (mle 'value 'upper)]]
    (conjp
     (mle (multiply 'factor 'upper) (multiply 'factor 'value))
     (mle (multiply 'factor 'value) (multiply 'factor 'lower))
     (app (function/const* 'matrix/multiply-antitone-right [])
          'factor 'value 'upper 'factor-negative 'upper-ordered)
     (app (function/const* 'matrix/multiply-antitone-right [])
          'factor 'lower 'value 'factor-negative 'lower-ordered)))})

(def definition-specs [])
(def theorem-specs
  [dot-bounds-nonnegative-weights-spec
   dot-bounds-nonpositive-weights-spec
   action-bounds-nonnegative-rows-spec
   action-bounds-nonpositive-rows-spec
   action-bounds-nonnegative-values-spec
   action-bounds-nonpositive-values-spec
   multiply-bounds-left-nonnegative-factor-spec
   multiply-bounds-left-nonpositive-factor-spec
   multiply-bounds-right-nonnegative-factor-spec
   multiply-bounds-right-nonpositive-factor-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.antitone])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-interval-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.interval-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
