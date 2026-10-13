(ns rainbow.math.linear.matrix.signed-scale
  "Arbitrary signed-scalar homogeneity for native finite matrices.

  The existing vector/signed-scale acts pointwise by an arbitrary signed
  rational.  Dot products are homogeneous in their second argument as well as
  their first, so native matrix action commutes with scaling its input.  Mapping
  the same action over matrix rows then gives an unrestricted left-factor
  homogeneity law for matrix multiplication.  These laws remain valid for
  ragged and empty matrices because every operation uses the same total list
  semantics.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.associativity-counterexample
             :as counterexample]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- list-map [mapping rows]
  (app (function/const* 'list/map [type-level type-level])
       vector-type vector-type mapping rows))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def dot-signed-scale-right-spec
  {:name 'vector/dot-signed-scale-right :universes []
   :type
   (function/forall
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot 'values (vector-signed-scale 'factor 'weights))
     (signed-multiply 'factor (dot 'values 'weights))))
   :value
   (function/lam
    [['factor signed] ['values vector-type] ['weights vector-type]]
    (let [scaled-weights (vector-signed-scale 'factor 'weights)
          start (dot 'values scaled-weights)
          commuted (dot scaled-weights 'values)
          scaled-commuted
          (signed-multiply 'factor (dot 'weights 'values))
          finish (signed-multiply 'factor (dot 'values 'weights))]
      (transitive
       start scaled-commuted finish
       (transitive
        start commuted scaled-commuted
        (app (function/const* 'vector/dot-commutative [])
             'values scaled-weights)
        (app (function/const* 'vector/dot-signed-scale-left [])
             'factor 'weights 'values))
       (app
        (function/const* 'signed/multiply-left-respects-equivalence [])
        (dot 'weights 'values)
        (dot 'values 'weights)
        'factor
        (app (function/const* 'vector/dot-commutative [])
             'weights 'values)))))} )

(def vector-multiply-signed-scale-spec
  {:name 'matrix/vector-multiply-signed-scale :universes []
   :type
   (function/forall
    [['factor signed] ['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply 'rows (vector-signed-scale 'factor 'values))
     (vector-signed-scale
      'factor (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['factor signed] ['rows matrix-type] ['values vector-type]]
    (let [scaled-values (vector-signed-scale 'factor 'values)
          motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows scaled-values)
            (vector-signed-scale
             'factor (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-homogeneous (app motive 'tail)]]
           (let [row-dot (dot 'row 'values)
                 product (signed-multiply 'factor row-dot)
                 difference
                 (app (function/const* 'signed/subtract [])
                      (app (function/const* 'signed/scale [])
                           (app (function/const* 'signed/positive []) 'factor)
                           row-dot)
                      (app (function/const* 'signed/scale [])
                           (app (function/const* 'signed/negative []) 'factor)
                           row-dot))]
             (conjoin
              (signed-equivalent (dot 'row scaled-values) difference)
              (vector-equivalent
               (vector-multiply 'tail scaled-values)
               (vector-signed-scale
                'factor (vector-multiply 'tail 'values)))
              (transitive
               (dot 'row scaled-values) product difference
               (app (function/const* 'vector/dot-signed-scale-right [])
                    'factor 'row 'values)
               (symmetric
                difference product
                (app
                 (function/const* 'signed/scale-difference-multiply [])
                 'factor row-dot)))
              'tail-homogeneous)))]
      (matrix-rec motive trivial step 'rows)))} )

(def signed-scale-spec
  {:name 'matrix/signed-scale :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed matrix-type matrix-type)
   :value
   (function/lam
    [['factor signed] ['rows matrix-type]]
    (list-map
     (function/lam
      [['row vector-type]]
      (vector-signed-scale 'factor 'row))
     'rows))})

(def multiply-signed-scale-left-spec
  {:name 'matrix/multiply-signed-scale-left :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (multiply (matrix-signed-scale 'factor 'left) 'right)
     (matrix-signed-scale 'factor (multiply 'left 'right))))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]]
    (let [right-columns (transpose 'right)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply (matrix-signed-scale 'factor 'current-left) 'right)
            (matrix-signed-scale
             'factor (multiply 'current-left 'right))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-homogeneous (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-multiply
              right-columns (vector-signed-scale 'factor 'row))
             (vector-signed-scale
              'factor (vector-multiply right-columns 'row)))
            (matrix-equivalent
             (multiply (matrix-signed-scale 'factor 'tail) 'right)
             (matrix-signed-scale
              'factor (multiply 'tail 'right)))
            (app
             (function/const* 'matrix/vector-multiply-signed-scale [])
             'factor right-columns 'row)
            'tail-homogeneous))]
      (matrix-rec motive trivial step 'left)))} )

(def definition-specs [signed-scale-spec])
(def theorem-specs
  [dot-signed-scale-right-spec
   vector-multiply-signed-scale-spec
   multiply-signed-scale-left-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.associativity-counterexample])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-signed-scale (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.signed-scale))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
