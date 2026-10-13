(ns rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness
  "Fixed-point uniqueness for row-sum-contractive signed affine systems.

  The row-sum Lipschitz theorem bounds the distance between affine images.  If
  both inputs are fixed points, sup-distance congruence transports that bound
  to a self-bound `d <= rate*d`.  A supplied scalar collapse certificate turns
  every nonnegative self-bounded distance into zero, and fixed-shape separation
  then identifies the two vectors.  Keeping collapse explicit cleanly separates
  matrix geometry from the chosen strict-rate arithmetic.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.row-sum-lipschitz :as lipschitz]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.signed.vector-sup-congruence :as congruence]
            [rainbow.math.rational.signed.vector-sup-separation :as separation]))

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
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
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
   (vector-at-most (zero-like 'row) 'row)))
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))
(defn- collapse-certificate [rate]
  (function/forall
   [['distance signed]
    ['distance-nonnegative (sle signed-zero 'distance)]
    ['self-bound (sle 'distance (multiply rate 'distance))]]
   (veq 'distance signed-zero)))
(defn- fixed-point-binders []
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] ['right vector-type]
   ['rate signed]
   ['rate-nonnegative (sle signed-zero 'rate)]
   ['shape (same-shape 'left 'right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (row-sums-bounded 'rows 'rate)]
   ['left-fixed
    (vector-equivalent (affine-action 'rows 'offset 'left) 'left)]
   ['right-fixed
    (vector-equivalent (affine-action 'rows 'offset 'right) 'right)]
   ['collapse (collapse-certificate 'rate)]])

(def fixed-points-have-zero-sup-distance-spec
  (let [distance (sup-distance 'left 'right)
        image-left (affine-action 'rows 'offset 'left)
        image-right (affine-action 'rows 'offset 'right)
        image-distance (sup-distance image-left image-right)
        scaled-distance (multiply 'rate distance)]
    {:name 'matrix/affine-row-sum-fixed-points-have-zero-sup-distance
     :universes []
     :type
     (function/forall (fixed-point-binders)
                      (veq distance signed-zero))
     :value
     (function/lam
      (fixed-point-binders)
      (let [image-bound
            (app
             (function/const*
              'matrix/affine-action-row-sum-lipschitz [])
             'rows 'offset 'left 'right 'rate
             'rate-nonnegative 'shape 'offset-shape
             'positive-rows 'bounded-sums)
            fixed-distance
            (app
             (function/const*
              'vector/sup-distance-respects-equivalence [])
             image-left 'left image-right 'right
             'left-fixed 'right-fixed)
            self-bound
            (app
             (function/const*
              'signed/at-most-respects-equivalence [])
             image-distance distance
             scaled-distance scaled-distance
             fixed-distance
             (app (function/const*
                   'signed/equivalent-reflexive [])
                  scaled-distance)
             image-bound)
            distance-nonnegative
            (app (function/const*
                  'vector/sup-distance-nonnegative [])
                 'left 'right)]
        (app 'collapse distance distance-nonnegative self-bound)))}))

(def fixed-points-unique-spec
  {:name 'matrix/affine-row-sum-fixed-points-unique :universes []
   :type
   (function/forall (fixed-point-binders)
                    (vector-equivalent 'left 'right))
   :value
   (function/lam
    (fixed-point-binders)
    (let [distance-zero
          (app
           (function/const*
            'matrix/affine-row-sum-fixed-points-have-zero-sup-distance [])
           'rows 'offset 'left 'right 'rate
           'rate-nonnegative 'shape 'offset-shape
           'positive-rows 'bounded-sums
           'left-fixed 'right-fixed 'collapse)]
      (app
       (function/const*
        'vector/equivalent-of-sup-distance-zero [])
       'left 'right 'shape distance-zero)))})

(def definition-specs [])
(def theorem-specs
  [fixed-points-have-zero-sup-distance-spec
   fixed-points-unique-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing
      current (:name spec) milestone spec))
   env specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.row-sum-lipschitz])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/at-most-respects-equivalence :signed-order-respects order-respects/at-most-respects-equivalence-spec) (extend-specs-if-missing :signed-vector-sup-congruence congruence/theorem-specs) (extend-spec-if-missing 'vector/equivalent-of-sup-distance-zero :signed-vector-sup-separation separation/equivalent-of-sup-distance-zero-spec) (support/extend-with :finite-matrix-row-sum-fixed-point-uniqueness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
