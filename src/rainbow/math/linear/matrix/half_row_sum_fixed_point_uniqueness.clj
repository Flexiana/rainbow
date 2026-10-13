(ns rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness
  "Concrete half-contractive uniqueness for signed affine row-sum systems.

  The signed embedding of 1/2 adds to one, so two copies of `d <= (1/2)d`
  yield `d+d <= d`.  Additive order cancellation gives `d <= 0`; combined
  with nonnegativity, antisymmetry gives `d ~ 0`.  This discharges the abstract
  collapse certificate used by the generic row-sum fixed-point theorem and
  produces a premise-complete half-rate affine uniqueness result.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness
             :as generic]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.farkas-elim-list :as nnrat-bounds]
            [rainbow.math.rational.value :as rational-value]
            [rainbow.math.rational.signed.order-cancellation :as cancellation]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
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
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
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
(defn- half-row-sums [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) signed-half)))
(defn- half-fixed-point-binders []
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] ['right vector-type]
   ['shape (same-shape 'left 'right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (half-row-sums 'rows)]
   ['left-fixed
    (vector-equivalent (affine-action 'rows 'offset 'left) 'left)]
   ['right-fixed
    (vector-equivalent (affine-action 'rows 'offset 'right) 'right)]])

(defn- rat-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- rat-add-respects [left left-prime right right-prime
                         left-same right-same]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))

(def signed-half-add-half-spec
  {:name 'signed/half-add-half :universes []
   :type (veq (sadd signed-half signed-half) signed-one)
   :value
   (let [half-sum (radd nnrat-half nnrat-half)
         zero-sum (radd nnrat-zero nnrat-zero)
         left (radd half-sum nnrat-zero)
         right (radd nnrat-one zero-sum)
         zero-sum-zero
         (app (function/const* 'nnrat/add-zero-right []) nnrat-zero)
         right-one
         (rat-transitive
          right (radd nnrat-one nnrat-zero) nnrat-one
          (rat-add-respects
           nnrat-one nnrat-one zero-sum nnrat-zero
           (rat-reflexive nnrat-one) zero-sum-zero)
          (app (function/const* 'nnrat/add-zero-right []) nnrat-one))]
     (rat-transitive
      left half-sum right
      (app (function/const* 'nnrat/add-zero-right []) half-sum)
      (rat-transitive
       half-sum nnrat-one right
       (function/const* 'rvalue/half-plus-half [])
       (rat-symmetric right nnrat-one right-one))))})

(def signed-half-scale-add-self-spec
  {:name 'signed/half-scale-add-self :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (sadd (smul signed-half 'value)
               (smul signed-half 'value))
         'value))
   :value
   (function/lam
    [['value signed]]
    (let [half-scaled (smul signed-half 'value)
          split (sadd half-scaled half-scaled)
          combined (smul (sadd signed-half signed-half) 'value)
          one-scaled (smul signed-one 'value)]
      (signed-transitive
       split combined 'value
       (signed-symmetric
        combined split
        (app (function/const*
              'signed/multiply-distributes-add-right [])
             signed-half signed-half 'value))
       (signed-transitive
        combined one-scaled 'value
        (app (function/const*
              'signed/multiply-right-respects-equivalence [])
             (sadd signed-half signed-half) signed-one 'value
             (function/const* 'signed/half-add-half []))
        (app (function/const* 'signed/multiply-one-left [])
             'value)))))})

(def signed-zero-at-most-half-spec
  {:name 'signed/zero-at-most-half :universes []
   :type (sle signed-zero signed-half)
   :value
   (app
    (function/const* 'signed/zero-at-most-of-nonnegative [])
    signed-half
    (app (function/const* 'nnrat/zero-at-most []) nnrat-half))})

(def signed-half-contraction-collapse-spec
  {:name 'signed/half-contraction-collapse :universes []
   :type
   (function/forall
    [['distance signed]
     ['distance-nonnegative (sle signed-zero 'distance)]
     ['self-bound
      (sle 'distance (smul signed-half 'distance))]]
    (veq 'distance signed-zero))
   :value
   (function/lam
    [['distance signed]
     ['distance-nonnegative (sle signed-zero 'distance)]
     ['self-bound
      (sle 'distance (smul signed-half 'distance))]]
    (let [half-distance (smul signed-half 'distance)
          doubled (sadd 'distance 'distance)
          doubled-half (sadd half-distance half-distance)
          summed-bound
          (app (function/const* 'signed/add-monotone [])
               'distance half-distance 'distance half-distance
               'self-bound 'self-bound)
          double-at-most-distance
          (order-respects
           doubled doubled doubled-half 'distance
           (signed-reflexive doubled)
           (app (function/const* 'signed/half-scale-add-self [])
                'distance)
           summed-bound)
          padded-distance (sadd 'distance signed-zero)
          distance-to-padded
          (signed-symmetric
           padded-distance 'distance
           (app (function/const* 'signed/add-zero-right [])
                'distance))
          double-at-most-padded
          (order-respects
           doubled doubled 'distance padded-distance
           (signed-reflexive doubled) distance-to-padded
           double-at-most-distance)
          distance-at-most-zero
          (app (function/const* 'signed/at-most-add-left-cancel [])
               'distance signed-zero 'distance
               double-at-most-padded)]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'distance signed-zero
           distance-at-most-zero 'distance-nonnegative)))})

(def affine-half-fixed-points-have-zero-sup-distance-spec
  {:name 'matrix/affine-half-row-sum-fixed-points-have-zero-sup-distance
   :universes []
   :type
   (function/forall
    (half-fixed-point-binders)
    (veq (sup-distance 'left 'right) signed-zero))
   :value
   (function/lam
    (half-fixed-point-binders)
    (app
     (function/const*
      'matrix/affine-row-sum-fixed-points-have-zero-sup-distance [])
     'rows 'offset 'left 'right signed-half
     (function/const* 'signed/zero-at-most-half [])
     'shape 'offset-shape 'positive-rows 'bounded-sums
     'left-fixed 'right-fixed
     (function/const* 'signed/half-contraction-collapse [])))})

(def affine-half-fixed-points-unique-spec
  {:name 'matrix/affine-half-row-sum-fixed-points-unique :universes []
   :type
   (function/forall
    (half-fixed-point-binders)
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    (half-fixed-point-binders)
    (app
     (function/const* 'matrix/affine-row-sum-fixed-points-unique [])
     'rows 'offset 'left 'right signed-half
     (function/const* 'signed/zero-at-most-half [])
     'shape 'offset-shape 'positive-rows 'bounded-sums
     'left-fixed 'right-fixed
     (function/const* 'signed/half-contraction-collapse [])))})

(def definition-specs [])
(def theorem-specs
  [signed-half-add-half-spec
   signed-half-scale-add-self-spec
   signed-zero-at-most-half-spec
   signed-half-contraction-collapse-spec
   affine-half-fixed-points-have-zero-sup-distance-spec
   affine-half-fixed-points-unique-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'rvalue/half-plus-half :rational-value rational-value/half-plus-half-spec) (extend-spec-if-missing 'nnrat/zero-at-most :nnrat-farkas-elim-list nnrat-bounds/zero-at-most-spec) (extend-spec-if-missing 'signed/add-monotone :signed-order-monotone monotone/add-monotone-spec) (extend-spec-if-missing 'signed/at-most-add-left-cancel :signed-order-cancellation cancellation/add-left-cancel-spec) (support/extend-with :finite-matrix-half-row-sum-fixed-point-uniqueness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
