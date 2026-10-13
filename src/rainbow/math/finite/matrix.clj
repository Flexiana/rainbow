(ns rainbow.math.finite.matrix
  "Finite signed-rational matrices and their native action on vectors.

  A matrix is a List of signed-rational row vectors.  Matrix-vector
  multiplication maps the existing exact dot product over those rows:

    matrix/vector-multiply rows values = map (dot _ values) rows

  The first laws establish the operator interface needed by finite-dimensional
  OR: a zero-like input maps to a zero-like output, equivalent inputs map to
  equivalent outputs, and the operator preserves same-shaped vector addition.
  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.counterfactual-distance-laws :as distance-laws]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-add]
            [rainbow.math.linear.vector.dot-additive :as dot-additive]
            [rainbow.math.linear.vector.dot-bilinear :as bilinear]
            [rainbow.math.linear.vector.dot-congruence :as dot-congruence]
            [rainbow.math.linear.vector.dot-zero-laws :as zero-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def signed-zero (function/const* 'signed/zero []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- list-map [source target mapping values]
  (app (function/const* 'list/map [type-level type-level])
       source target mapping values))
(defn- list-rec [element motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       element motive base step values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def vector-multiply-spec
  {:name 'matrix/vector-multiply :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type vector-type vector-type)
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (list-map
     vector-type signed
     (function/lam [['row vector-type]] (dot 'row 'values))
     'rows))})

(def vector-multiply-zero-like-spec
  {:name 'matrix/vector-multiply-zero-like :universes []
   :type
   (function/forall
    [['rows matrix-type] ['values vector-type]]
    (vector-equivalent
     (vector-multiply 'rows (zero-like 'values))
     (zero-like (vector-multiply 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['values vector-type]]
    (let [zeros (zero-like 'values)
          motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows zeros)
            (zero-like (vector-multiply 'current-rows 'values))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-zero (app motive 'tail)]]
           (conjoin
            (signed-equivalent (dot 'row zeros) signed-zero)
            (vector-equivalent
             (vector-multiply 'tail zeros)
             (zero-like (vector-multiply 'tail 'values)))
            (app (function/const* 'vector/dot-zero-like-right [])
                 'row 'values)
            'tail-zero))]
      (list-rec vector-type motive trivial step 'rows)))})

(def vector-multiply-respects-equivalence-spec
  {:name 'matrix/vector-multiply-respects-equivalence :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent
     (vector-multiply 'rows 'left)
     (vector-multiply 'rows 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows 'left)
            (vector-multiply 'current-rows 'right)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-congruent (app motive 'tail)]]
           (conjoin
            (signed-equivalent (dot 'row 'left) (dot 'row 'right))
            (vector-equivalent
             (vector-multiply 'tail 'left)
             (vector-multiply 'tail 'right))
            (app
             (function/const*
              'vector/dot-right-respects-equivalence [])
             'row 'left 'right 'same)
            'tail-congruent))]
      (list-rec vector-type motive trivial step 'rows)))})

(def vector-multiply-additive-spec
  {:name 'matrix/vector-multiply-additive :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (vector-equivalent
     (vector-multiply 'rows (vector-add 'left 'right))
     (vector-add
      (vector-multiply 'rows 'left)
      (vector-multiply 'rows 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (let [sum (vector-add 'left 'right)
          motive
          (function/lam
           [['current-rows matrix-type]]
           (vector-equivalent
            (vector-multiply 'current-rows sum)
            (vector-add
             (vector-multiply 'current-rows 'left)
             (vector-multiply 'current-rows 'right))))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-additive (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (dot 'row sum)
             (app (function/const* 'signed/add [])
                  (dot 'row 'left) (dot 'row 'right)))
            (vector-equivalent
             (vector-multiply 'tail sum)
             (vector-add
              (vector-multiply 'tail 'left)
              (vector-multiply 'tail 'right)))
            (app (function/const* 'vector/dot-additive-right [])
                 'row 'left 'right 'shape)
            'tail-additive))]
      (list-rec vector-type motive trivial step 'rows)))})

(def definition-specs [vector-multiply-spec])
(def theorem-specs
  [vector-multiply-zero-like-spec
   vector-multiply-respects-equivalence-spec
   vector-multiply-additive-spec])

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
  (-> checked-environment (extend-spec-if-missing 'vector/dot-zero-like-right :vector-dot-zero-laws zero-laws/dot-zero-like-right-spec) (extend-spec-if-missing 'vector/dot-left-respects-equivalence :vector-dot-congruence dot-congruence/dot-left-respects-equivalence-spec) (extend-spec-if-missing 'vector/dot-right-respects-equivalence :vector-dot-congruence dot-congruence/dot-right-respects-equivalence-spec) (extend-spec-if-missing 'signed/multiply-distributes-add-right :signed-distributive distributive/multiply-distributes-add-right-spec) (extend-spec-if-missing 'signed/add-four-reorder :signed-map-sum-algebra signed-add/add-four-reorder-spec) (extend-spec-if-missing 'vector/dot-additive-left :vector-dot-additive dot-additive/dot-additive-left-spec) (extend-spec-if-missing 'vector/dot-additive-right :vector-dot-bilinear bilinear/dot-additive-right-spec) (support/extend-with :finite-matrix (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.matrix))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
