(ns rainbow.math.linear.matrix.subtract-linear
  "Subtraction commutes with native matrix action, transpose, and products.

  Same-shaped subtraction is addition of a same-shaped negation.  Reusing that
  shape certificate, additive bilinearity and negation linearity compose into
  action, transpose, and two-sided product subtraction laws.  Native and
  axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.negate-linear :as negate-linear]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & args] (apply function/app f args))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- matrix-subtract [left right]
  (app (function/const* 'matrix/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- vector-transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- matrix-transitive [left middle right first second]
  (app (function/const* 'matrix/equivalent-transitive [])
       left middle right first second))

(defn- same-shape-negated-right [left right same]
  (let [negated (matrix-negate right)
        negated-right
        (app (function/const* 'matrix/negate-preserves-same-shape [])
             right)
        right-negated
        (app (function/const* 'matrix/same-shape-symmetric [])
             negated right negated-right)]
    (app (function/const* 'matrix/same-shape-transitive [])
         left right negated same right-negated)))

(def vector-multiply-subtract-rows-spec
  {:name 'matrix/vector-multiply-subtract-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (vector-equivalent
     (vector-multiply (matrix-subtract 'left 'right) 'values)
     (vector-subtract
      (vector-multiply 'left 'values)
      (vector-multiply 'right 'values))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [negated (matrix-negate 'right)
          left-action (vector-multiply 'left 'values)
          negated-action (vector-multiply negated 'values)
          right-action (vector-multiply 'right 'values)
          start
          (vector-multiply (matrix-subtract 'left 'right) 'values)
          middle (vector-add left-action negated-action)
          finish (vector-subtract left-action right-action)
          additive-shape
          (same-shape-negated-right 'left 'right 'shape)]
      (vector-transitive
       start middle finish
       (app
        (function/const* 'matrix/vector-multiply-additive-rows [])
        'left negated 'values additive-shape)
       (app (function/const* 'vector/add-respects-equivalence [])
            left-action left-action
            negated-action (vector-negate right-action)
            (app (function/const* 'vector/equivalent-reflexive [])
                 left-action)
            (app
             (function/const* 'matrix/vector-multiply-negate-rows [])
             'right 'values)))))})

(def transpose-subtract-spec
  {:name 'matrix/transpose-subtract :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (transpose (matrix-subtract 'left 'right))
     (matrix-subtract (transpose 'left) (transpose 'right))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [negated (matrix-negate 'right)
          transposed-left (transpose 'left)
          transposed-negated (transpose negated)
          negated-transpose (matrix-negate (transpose 'right))
          start (transpose (matrix-subtract 'left 'right))
          middle (matrix-addition transposed-left transposed-negated)
          finish
          (matrix-subtract transposed-left (transpose 'right))
          additive-shape
          (same-shape-negated-right 'left 'right 'shape)]
      (matrix-transitive
       start middle finish
       (app (function/const* 'matrix/transpose-additive [])
            'left negated additive-shape)
       (app
        (function/const* 'matrix/add-respects-right-equivalence [])
        transposed-left transposed-negated negated-transpose
        (app (function/const* 'matrix/transpose-negate []) 'right)))))})

(def multiply-subtract-left-spec
  {:name 'matrix/multiply-subtract-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (multiply (matrix-subtract 'left 'right) 'factor)
     (matrix-subtract
      (multiply 'left 'factor)
      (multiply 'right 'factor))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [negated (matrix-negate 'right)
          left-product (multiply 'left 'factor)
          negated-product (multiply negated 'factor)
          right-product (multiply 'right 'factor)
          start (multiply (matrix-subtract 'left 'right) 'factor)
          middle (matrix-addition left-product negated-product)
          finish (matrix-subtract left-product right-product)
          additive-shape
          (same-shape-negated-right 'left 'right 'shape)]
      (matrix-transitive
       start middle finish
       (app (function/const* 'matrix/multiply-additive-left [])
            'left negated 'factor additive-shape)
       (app
        (function/const* 'matrix/add-respects-right-equivalence [])
        left-product negated-product (matrix-negate right-product)
        (app (function/const* 'matrix/multiply-negate-left [])
             'right 'factor)))))})

(def multiply-subtract-right-spec
  {:name 'matrix/multiply-subtract-right :universes []
   :type
   (function/forall
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (multiply 'factor (matrix-subtract 'left 'right))
     (matrix-subtract
      (multiply 'factor 'left)
      (multiply 'factor 'right))))
   :value
   (function/lam
    [['factor matrix-type] ['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [negated (matrix-negate 'right)
          left-product (multiply 'factor 'left)
          negated-product (multiply 'factor negated)
          right-product (multiply 'factor 'right)
          start (multiply 'factor (matrix-subtract 'left 'right))
          middle (matrix-addition left-product negated-product)
          finish (matrix-subtract left-product right-product)
          additive-shape
          (same-shape-negated-right 'left 'right 'shape)]
      (matrix-transitive
       start middle finish
       (app (function/const* 'matrix/multiply-additive-right [])
            'factor 'left negated additive-shape)
       (app
        (function/const* 'matrix/add-respects-right-equivalence [])
        left-product negated-product (matrix-negate right-product)
        (app (function/const* 'matrix/multiply-negate-right [])
             'factor 'right)))))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-subtract-rows-spec
   transpose-subtract-spec
   multiply-subtract-left-spec
   multiply-subtract-right-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.negate-linear])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-subtract-linear theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.subtract-linear))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
