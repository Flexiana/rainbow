(ns rainbow.math.linear.matrix.signed-scale-units
  "Scalar-factor additivity and zero/one laws for signed matrix scaling.

  The scale-difference representation distributes over addition in its signed
  factor, sends zero to shaped zero, and sends one to the original value.
  Structural lifts complete these module laws for vectors and matrices without
  shape premises.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-algebra :as algebra]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- vector-zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- matrix-zero-like [rows]
  (app (function/const* 'matrix/zero-like []) rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def scale-difference-additive-factor-spec
  {:name 'signed/scale-difference-additive-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['value signed]]
    (signed-equivalent
     (scale-difference (signed-add 'left 'right) 'value)
     (signed-add
      (scale-difference 'left 'value)
      (scale-difference 'right 'value))))
   :value
   (function/lam
    [['left signed] ['right signed] ['value signed]]
    (let [factor-sum (signed-add 'left 'right)
          start (scale-difference factor-sum 'value)
          product (signed-multiply factor-sum 'value)
          split
          (signed-add
           (signed-multiply 'left 'value)
           (signed-multiply 'right 'value))
          finish
          (signed-add
           (scale-difference 'left 'value)
           (scale-difference 'right 'value))]
      (signed-transitive
       start split finish
       (signed-transitive
        start product split
        (app (function/const* 'signed/scale-difference-multiply [])
             factor-sum 'value)
        (app
         (function/const* 'signed/multiply-distributes-add-right [])
         'left 'right 'value))
       (app (function/const* 'signed/add-respects-equivalence [])
            (signed-multiply 'left 'value)
            (scale-difference 'left 'value)
            (signed-multiply 'right 'value)
            (scale-difference 'right 'value)
            (signed-symmetric
             (scale-difference 'left 'value)
             (signed-multiply 'left 'value)
             (app
              (function/const* 'signed/scale-difference-multiply [])
              'left 'value))
            (signed-symmetric
             (scale-difference 'right 'value)
             (signed-multiply 'right 'value)
             (app
              (function/const* 'signed/scale-difference-multiply [])
              'right 'value))))))})

(def scale-difference-zero-spec
  {:name 'signed/scale-difference-zero :universes []
   :type
   (function/forall
    [['value signed]]
    (signed-equivalent
     (scale-difference signed-zero 'value)
     signed-zero))
   :value
   (function/lam
    [['value signed]]
    (signed-transitive
     (scale-difference signed-zero 'value)
     (signed-multiply signed-zero 'value)
     signed-zero
     (app (function/const* 'signed/scale-difference-multiply [])
          signed-zero 'value)
     (app (function/const* 'signed/multiply-zero-left []) 'value)))})

(def scale-difference-one-spec
  {:name 'signed/scale-difference-one :universes []
   :type
   (function/forall
    [['value signed]]
    (signed-equivalent
     (scale-difference signed-one 'value)
     'value))
   :value
   (function/lam
    [['value signed]]
    (signed-transitive
     (scale-difference signed-one 'value)
     (signed-multiply signed-one 'value)
     'value
     (app (function/const* 'signed/scale-difference-multiply [])
          signed-one 'value)
     (app (function/const* 'signed/multiply-one-left []) 'value)))})

(def vector-signed-scale-additive-factor-spec
  {:name 'vector/signed-scale-additive-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale (signed-add 'left 'right) 'values)
     (vector-add
      (vector-signed-scale 'left 'values)
      (vector-signed-scale 'right 'values))))
   :value
   (function/lam
    [['left signed] ['right signed] ['values vector-type]]
    (let [factor-sum (signed-add 'left 'right)
          motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale factor-sum 'current)
            (vector-add
             (vector-signed-scale 'left 'current)
             (vector-signed-scale 'right 'current))))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-additive (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference factor-sum 'head)
             (signed-add
              (scale-difference 'left 'head)
              (scale-difference 'right 'head)))
            (vector-equivalent
             (vector-signed-scale factor-sum 'tail)
             (vector-add
              (vector-signed-scale 'left 'tail)
              (vector-signed-scale 'right 'tail)))
            (app
             (function/const*
              'signed/scale-difference-additive-factor [])
             'left 'right 'head)
            'tail-additive))]
      (vector-rec motive trivial step 'values)))})

(def vector-signed-scale-zero-spec
  {:name 'vector/signed-scale-zero :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-signed-scale signed-zero 'values)
     (vector-zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale signed-zero 'current)
            (vector-zero-like 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-zero (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference signed-zero 'head) signed-zero)
            (vector-equivalent
             (vector-signed-scale signed-zero 'tail)
             (vector-zero-like 'tail))
            (app (function/const* 'signed/scale-difference-zero [])
                 'head)
            'tail-zero))]
      (vector-rec motive trivial step 'values)))})

(def vector-signed-scale-one-spec
  {:name 'vector/signed-scale-one :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-signed-scale signed-one 'values)
     'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale signed-one 'current)
            'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-one (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference signed-one 'head) 'head)
            (vector-equivalent
             (vector-signed-scale signed-one 'tail) 'tail)
            (app (function/const* 'signed/scale-difference-one [])
                 'head)
            'tail-one))]
      (vector-rec motive trivial step 'values)))})

(def matrix-signed-scale-additive-factor-spec
  {:name 'matrix/signed-scale-additive-factor :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale (signed-add 'left 'right) 'rows)
     (matrix-addition
      (matrix-signed-scale 'left 'rows)
      (matrix-signed-scale 'right 'rows))))
   :value
   (function/lam
    [['left signed] ['right signed] ['rows matrix-type]]
    (let [factor-sum (signed-add 'left 'right)
          motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale factor-sum 'current)
            (matrix-addition
             (matrix-signed-scale 'left 'current)
             (matrix-signed-scale 'right 'current))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-additive (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale factor-sum 'row)
             (vector-add
              (vector-signed-scale 'left 'row)
              (vector-signed-scale 'right 'row)))
            (matrix-equivalent
             (matrix-signed-scale factor-sum 'tail)
             (matrix-addition
              (matrix-signed-scale 'left 'tail)
              (matrix-signed-scale 'right 'tail)))
            (app
             (function/const* 'vector/signed-scale-additive-factor [])
             'left 'right 'row)
            'tail-additive))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-zero-spec
  {:name 'matrix/signed-scale-zero :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale signed-zero 'rows)
     (matrix-zero-like 'rows)))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale signed-zero 'current)
            (matrix-zero-like 'current)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-zero (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale signed-zero 'row)
             (vector-zero-like 'row))
            (matrix-equivalent
             (matrix-signed-scale signed-zero 'tail)
             (matrix-zero-like 'tail))
            (app (function/const* 'vector/signed-scale-zero []) 'row)
            'tail-zero))]
      (matrix-rec motive trivial step 'rows)))})

(def matrix-signed-scale-one-spec
  {:name 'matrix/signed-scale-one :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale signed-one 'rows)
     'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale signed-one 'current)
            'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-one (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale signed-one 'row) 'row)
            (matrix-equivalent
             (matrix-signed-scale signed-one 'tail) 'tail)
            (app (function/const* 'vector/signed-scale-one []) 'row)
            'tail-one))]
      (matrix-rec motive trivial step 'rows)))})

(def definition-specs [])
(def theorem-specs
  [scale-difference-additive-factor-spec
   scale-difference-zero-spec
   scale-difference-one-spec
   vector-signed-scale-additive-factor-spec
   vector-signed-scale-zero-spec
   vector-signed-scale-one-spec
   matrix-signed-scale-additive-factor-spec
   matrix-signed-scale-zero-spec
   matrix-signed-scale-one-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.signed-scale-algebra])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/multiply-zero-left :signed-distributive distributive/multiply-zero-left-spec) (extend-spec-if-missing 'signed/multiply-distributes-add-right :signed-distributive distributive/multiply-distributes-add-right-spec) (extend-spec-if-missing 'signed/multiply-one-left :signed-unit-laws unit-laws/multiply-one-left-spec) (support/extend-with :finite-matrix-signed-scale-units theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.signed-scale-units))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
