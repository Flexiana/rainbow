(ns rainbow.math.linear.matrix.linear
  "Shape and scalar-linearity laws for native matrix-vector multiplication.

    matrix/vector-multiply-output-shape
    matrix/vector-multiply-negate
    matrix/vector-multiply-scale

  The output length is determined solely by the number of rows, even for a
  ragged matrix.  Row-wise dot-product laws then show that the matrix action
  commutes with vector negation and nonnegative-rational scaling.  Native and
  axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.matrix :as matrix]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.scale-additive :as scale-additive]
            [rainbow.math.temporal-difference :as temporal-difference]
            [rainbow.math.linear.vector.dot-scale :as dot-scale]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step values))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def vector-multiply-output-shape-spec
  {:name 'matrix/vector-multiply-output-shape :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]]
    (same-shape
     (vector-multiply 'rows 'left)
     (vector-multiply 'rows 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (same-shape
            (vector-multiply 'current-rows 'left)
            (vector-multiply 'current-rows 'right)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (signed-equivalent signed-zero signed-zero)
            (same-shape
             (vector-multiply 'tail 'left)
             (vector-multiply 'tail 'right))
            (app (function/const* 'signed/equivalent-reflexive [])
                 signed-zero)
            'tail-shape))]
      (list-rec motive trivial step 'rows)))})

(def vector-multiply-negate-spec
  {:name 'matrix/vector-multiply-negate :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply 'rows (vector-negate 'values))
     (vector-negate (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (let [negated (vector-negate 'values)
          motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows negated)
            (vector-negate (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-negates (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (dot 'row negated)
             (signed-negate (dot 'row 'values)))
            (vector-equivalent
             (vector-multiply 'tail negated)
             (vector-negate (vector-multiply 'tail 'values)))
            (app (function/const* 'vector/dot-negate-right [])
                 'row 'values)
            'tail-negates))]
      (list-rec motive trivial step 'rows)))})

(def vector-multiply-scale-spec
  {:name 'matrix/vector-multiply-scale :universes []
   :type
   (function/forall
    [['rate nnrat] ['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply 'rows (vector-scale 'rate 'values))
     (vector-scale 'rate (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['rate nnrat] ['rows matrix-type] ['values vector-type]]
    (let [scaled (vector-scale 'rate 'values)
          motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows scaled)
            (vector-scale
             'rate (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-scales (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (dot 'row scaled)
             (signed-scale 'rate (dot 'row 'values)))
            (vector-equivalent
             (vector-multiply 'tail scaled)
             (vector-scale
              'rate (vector-multiply 'tail 'values)))
            (app (function/const* 'vector/dot-scale-right [])
                 'rate 'row 'values)
            'tail-scales))]
      (list-rec motive trivial step 'rows)))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-output-shape-spec
   vector-multiply-negate-spec
   vector-multiply-scale-spec])

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

(defn extend-environment [checked-environment]
  (-> checked-environment
      matrix/extend-environment
      (extend-spec-if-missing
       'signed/scale :temporal-difference temporal-difference/scale-spec)
      (extend-spec-if-missing
       'vector/scale :finite-vector finite-vector/scale-spec)
      (extend-spec-if-missing
       'signed/scale-additive :signed-scale-additive
       scale-additive/scale-additive-spec)
      (extend-specs-if-missing :vector-dot-scale dot-scale/theorem-specs)
      (support/extend-with :finite-matrix-linear theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
