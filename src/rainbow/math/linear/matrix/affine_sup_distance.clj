(ns rainbow.math.linear.matrix.affine-sup-distance
  "Sup-distance cancellation and bound transfer for signed affine action.

  Matrix-vector output length depends only on the row list.  Consequently one
  certificate that the affine offset has the action-output shape also covers
  every other input to the same matrix.  Fixed-shape vector translation then
  cancels the common offset exactly, and the order corollary transfers any
  linear-action distance bound to the affine map.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-order :as affine]
            [rainbow.math.linear.matrix.linear :as linear]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-translation :as translation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))

(def affine-action-sup-distance-cancels-offset-spec
  {:name 'matrix/affine-action-sup-distance-cancels-offset :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]]
    (veq
     (sup-distance (affine-action 'rows 'offset 'left)
                   (affine-action 'rows 'offset 'right))
     (sup-distance (action 'rows 'left)
                   (action 'rows 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]]
    (let [left-action (action 'rows 'left)
          right-action (action 'rows 'right)
          outputs-shape
          (app
           (function/const* 'matrix/vector-multiply-output-shape [])
           'rows 'left 'right)
          right-offset-shape
          (app (function/const* 'vector/same-shape-transitive [])
               'offset left-action right-action
               'offset-shape outputs-shape)]
      (app
       (function/const*
        'vector/sup-distance-add-left-same-shape [])
       'offset left-action right-action
       'offset-shape right-offset-shape)))})

(def affine-action-sup-distance-bounded-spec
  {:name 'matrix/affine-action-sup-distance-bounded :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type] ['upper signed]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['linear-bound
      (sle (sup-distance (action 'rows 'left)
                         (action 'rows 'right))
           'upper)]]
    (sle
     (sup-distance (affine-action 'rows 'offset 'left)
                   (affine-action 'rows 'offset 'right))
     'upper))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type] ['upper signed]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['linear-bound
      (sle (sup-distance (action 'rows 'left)
                         (action 'rows 'right))
           'upper)]]
    (let [affine-distance
          (sup-distance (affine-action 'rows 'offset 'left)
                        (affine-action 'rows 'offset 'right))
          linear-distance
          (sup-distance (action 'rows 'left)
                        (action 'rows 'right))
          same
          (app
           (function/const*
            'matrix/affine-action-sup-distance-cancels-offset [])
           'rows 'offset 'left 'right 'offset-shape)]
      (order-transitive
       affine-distance linear-distance 'upper
       (app (function/const* 'signed/equivalent-to-at-most [])
            affine-distance linear-distance same)
       'linear-bound)))})

(def definition-specs [])
(def theorem-specs
  [affine-action-sup-distance-cancels-offset-spec
   affine-action-sup-distance-bounded-spec])

(defn extend-environment [env]
  (-> env
      affine/extend-environment
      linear/extend-environment
      translation/extend-environment
      (support/extend-with :finite-matrix-affine-sup-distance theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
