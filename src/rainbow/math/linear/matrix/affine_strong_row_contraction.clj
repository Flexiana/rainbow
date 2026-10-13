(ns rainbow.math.linear.matrix.affine-strong-row-contraction
  "User-facing contraction results for any NNRAT row bound gamma <= 1/2.

  Row sums are signed because matrix entries are signed, while practical
  discount/rate certificates are nonnegative rationals.  The quotient-safe
  embedding sends `0 <= gamma <= 1/2` into signed order.  Transitivity then
  turns actual-row bounds `sum(row) <= from-nnrat(gamma)` into the half-row
  premises required by the established uniqueness, finite-horizon rate, and
  rate-null convergence theorems.  Native, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.math.linear.matrix.affine-half-iterate-converges
             :as convergence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def signed-half
  (function/app (function/const* 'signed/from-nnrat []) nnrat-half))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null [])
       sequence modulus))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- gamma-half [gamma gamma-at-most-half]
  (app (function/const* 'signed/from-nnrat-at-most [])
       gamma nnrat-half gamma-at-most-half))
(defn- half-bounded-sums [rows gamma gamma-at-most-half bounded-sums]
  (function/lam
   [['row vector-type] ['member (membership rows 'row)]]
   (order-transitive
    (vector-sum 'row) (from-nnrat gamma) signed-half
    (app bounded-sums 'row 'member)
    (gamma-half gamma gamma-at-most-half))))

(def zero-at-most-from-nnrat-spec
  {:name 'signed/zero-at-most-from-nnrat :universes []
   :type
   (function/forall
    [['value nnrat]]
    (sle signed-zero (from-nnrat 'value)))
   :value
   (function/lam
    [['value nnrat]]
    (app (function/const* 'signed/from-nnrat-at-most [])
         nnrat-zero 'value
         (app (function/const* 'nnrat/zero-at-most []) 'value)))})

(def nnrat-row-sums-imply-half-bound-spec
  {:name 'matrix/nnrat-row-sums-imply-half-bound :universes []
   :type
   (function/forall
    [['rows matrix-type] ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat 'gamma))]]
    (row-sums-bounded 'rows signed-half))
   :value
   (function/lam
    [['rows matrix-type] ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['bounded-sums
      (row-sums-bounded 'rows (from-nnrat 'gamma))]]
    (half-bounded-sums
     'rows 'gamma 'gamma-at-most-half 'bounded-sums))})

(defn- strong-row-binders [right]
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] [right vector-type]
   ['gamma nnrat]
   ['gamma-at-most-half (rle 'gamma nnrat-half)]
   ['shape (same-shape 'left right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat 'gamma))]])

(defn- fixed-binders []
  (into
   (strong-row-binders 'right)
   [['left-fixed
     (vector-equivalent (affine-action 'rows 'offset 'left) 'left)]
    ['right-fixed
     (vector-equivalent (affine-action 'rows 'offset 'right) 'right)]]))

(def strong-row-fixed-points-have-zero-sup-distance-spec
  {:name 'matrix/affine-nnrat-strong-row-fixed-points-have-zero-sup-distance
   :universes []
   :type
   (function/forall
    (fixed-binders)
    (veq (sup-distance 'left 'right) signed-zero))
   :value
   (function/lam
    (fixed-binders)
    (app
     (function/const*
      'matrix/affine-half-row-sum-fixed-points-have-zero-sup-distance [])
     'rows 'offset 'left 'right
     'shape 'offset-shape 'positive-rows
     (half-bounded-sums
      'rows 'gamma 'gamma-at-most-half 'bounded-sums)
     'left-fixed 'right-fixed))})

(def strong-row-fixed-points-unique-spec
  {:name 'matrix/affine-nnrat-strong-row-fixed-points-unique :universes []
   :type
   (function/forall
    (fixed-binders)
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    (fixed-binders)
    (app
     (function/const* 'matrix/affine-half-row-sum-fixed-points-unique [])
     'rows 'offset 'left 'right
     'shape 'offset-shape 'positive-rows
     (half-bounded-sums
      'rows 'gamma 'gamma-at-most-half 'bounded-sums)
     'left-fixed 'right-fixed))})

(def strong-row-iterate-sup-distance-rate-spec
  (let [binders (conj (strong-row-binders 'right) ['steps nat])]
    {:name 'matrix/affine-nnrat-strong-row-iterate-sup-distance-rate
     :universes []
     :type
     (function/forall
      binders
      (sle
       (sup-distance
        (affine-iterate 'rows 'offset 'steps 'left)
        (affine-iterate 'rows 'offset 'steps 'right))
       (half-power-scale 'steps (sup-distance 'left 'right))))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-half-iterate-sup-distance-rate [])
       'rows 'offset 'left 'right
       'shape 'offset-shape 'positive-rows
       (half-bounded-sums
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'steps))}))

(def strong-row-iterate-sup-distance-rate-null-spec
  (let [binders
        (conj
         (strong-row-binders 'right)
         ['initial-distance-at-most-one
          (sle (sup-distance 'left 'right) signed-one)])
        error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          (affine-iterate 'rows 'offset 'n 'right)))]
    {:name 'matrix/affine-nnrat-strong-row-iterate-sup-distance-rate-null
     :universes []
     :type
     (function/forall
      binders
      (signed-rate-null error (function/lam [['k nat]] 'k)))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-half-iterate-sup-distance-rate-null [])
       'rows 'offset 'left 'right
       'shape 'offset-shape 'positive-rows
       (half-bounded-sums
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'initial-distance-at-most-one))}))

(def strong-row-iterate-converges-to-fixed-point-spec
  (let [binders
        (into
         (strong-row-binders 'fixed-point)
         [['initial-distance-at-most-one
           (sle (sup-distance 'left 'fixed-point) signed-one)]
          ['fixed
           (vector-equivalent
            (affine-action 'rows 'offset 'fixed-point)
            'fixed-point)]])
        error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          'fixed-point))]
    {:name 'matrix/affine-nnrat-strong-row-iterate-converges-to-fixed-point
     :universes []
     :type
     (function/forall
      binders
      (signed-rate-null error (function/lam [['k nat]] 'k)))
     :value
     (function/lam
      binders
      (app
       (function/const*
        'matrix/affine-half-iterate-converges-to-fixed-point [])
       'rows 'offset 'left 'fixed-point
       'shape 'offset-shape 'positive-rows
       (half-bounded-sums
        'rows 'gamma 'gamma-at-most-half 'bounded-sums)
       'initial-distance-at-most-one 'fixed))}))

(def definition-specs [])
(def theorem-specs
  [zero-at-most-from-nnrat-spec
   nnrat-row-sums-imply-half-bound-spec
   strong-row-fixed-points-have-zero-sup-distance-spec
   strong-row-fixed-points-unique-spec
   strong-row-iterate-sup-distance-rate-spec
   strong-row-iterate-sup-distance-rate-null-spec
   strong-row-iterate-converges-to-fixed-point-spec])

(defn extend-environment [env]
  (-> env
      convergence/extend-environment
      (support/extend-with
       :finite-matrix-affine-strong-row-contraction theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
