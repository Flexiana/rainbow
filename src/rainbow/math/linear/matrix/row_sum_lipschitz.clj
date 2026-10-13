(ns rainbow.math.linear.matrix.row-sum-lipschitz
  "Sup-Lipschitz bounds for nonnegative row-sum-bounded affine matrices.

  Premises quantify over the rows actually present in the matrix: every member
  row is componentwise nonnegative and has signed sum at most `rate`.  The sharp
  row theorem bounds each dot-product distance by row mass times input sup
  distance; monotonic scaling replaces row mass by `rate`; the structural matrix
  lift takes the output maximum.  Common-offset cancellation gives the affine
  theorem with the same rate.  A later strict-rate certificate can use this as
  the contraction premise.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.action-sup-bound :as action-bound]
            [rainbow.math.linear.matrix.affine-sup-distance :as affine-bound]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]
            [rainbow.math.linear.vector.row-sum-lipschitz :as row-bound]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-positive [values]
  (vector-at-most (zero-like values) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- dot [row values]
  (app (function/const* 'vector/dot []) row values))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-positive 'row)))
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- multiply-nonnegative-at-most [left right left-positive right-positive]
  (let [product (multiply left right)]
    (app
     (function/const* 'signed/zero-at-most-of-nonnegative [])
     product
     (app
      (function/const* 'signed/multiply-nonnegative [])
      left right
      (app (function/const* 'signed/nonnegative-of-zero-at-most [])
           left left-positive)
      (app (function/const* 'signed/nonnegative-of-zero-at-most [])
           right right-positive)))))

(def vector-multiply-row-sum-lipschitz-spec
  {:name 'matrix/vector-multiply-row-sum-lipschitz :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rate signed]
     ['rate-nonnegative (sle signed-zero 'rate)]
     ['shape (same-shape 'left 'right)]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'rate)]]
    (sle
     (sup-distance (action 'rows 'left)
                   (action 'rows 'right))
     (multiply 'rate (sup-distance 'left 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['rate signed]
     ['rate-nonnegative (sle signed-zero 'rate)]
     ['shape (same-shape 'left 'right)]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'rate)]]
    (let [input-distance (sup-distance 'left 'right)
          upper (multiply 'rate input-distance)
          input-nonnegative
          (app (function/const* 'vector/sup-distance-nonnegative [])
               'left 'right)
          upper-nonnegative
          (multiply-nonnegative-at-most
           'rate input-distance 'rate-nonnegative input-nonnegative)
          rowwise
          (function/lam
           [['row vector-type] ['member (membership 'rows 'row)]]
           (let [row-mass (vector-sum 'row)
                 row-upper (multiply row-mass input-distance)
                 row-distance
                 (scalar-distance (dot 'row 'left)
                                  (dot 'row 'right))
                 sharp-bound
                 (app
                  (function/const*
                   'vector/dot-distance-bounded-by-row-sum [])
                  'row 'left 'right
                  (app 'positive-rows 'row 'member)
                  'shape)
                 rate-bound
                 (app
                  (function/const* 'signed/multiply-right-monotone [])
                  input-distance row-mass 'rate
                  input-nonnegative
                  (app 'bounded-sums 'row 'member))]
             (order-transitive
              row-distance row-upper upper
              sharp-bound rate-bound)))]
      (app
       (function/const*
        'matrix/vector-multiply-sup-distance-bounded [])
       'rows 'left 'right upper upper-nonnegative rowwise)))})

(def affine-action-row-sum-lipschitz-spec
  {:name 'matrix/affine-action-row-sum-lipschitz :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rate signed]
     ['rate-nonnegative (sle signed-zero 'rate)]
     ['shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'rate)]]
    (sle
     (sup-distance (affine-action 'rows 'offset 'left)
                   (affine-action 'rows 'offset 'right))
     (multiply 'rate (sup-distance 'left 'right))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rate signed]
     ['rate-nonnegative (sle signed-zero 'rate)]
     ['shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'rate)]]
    (let [upper (multiply 'rate (sup-distance 'left 'right))
          linear-bound
          (app
           (function/const*
            'matrix/vector-multiply-row-sum-lipschitz [])
           'rows 'left 'right 'rate
           'rate-nonnegative 'shape
           'positive-rows 'bounded-sums)]
      (app
       (function/const*
        'matrix/affine-action-sup-distance-bounded [])
       'rows 'offset 'left 'right upper
       'offset-shape linear-bound)))})

(def definition-specs [])
(def theorem-specs
  [vector-multiply-row-sum-lipschitz-spec
   affine-action-row-sum-lipschitz-spec])

(defn extend-environment [env]
  (-> env
      row-bound/extend-environment
      action-bound/extend-environment
      affine-bound/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      sup/extend-environment
      (support/extend-with :finite-matrix-row-sum-lipschitz theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
