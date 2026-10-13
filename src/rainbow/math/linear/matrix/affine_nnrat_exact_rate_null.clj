(ns rainbow.math.linear.matrix.affine-nnrat-exact-rate-null
  "Null-sequence bridges for exact NNRAT contraction envelopes.

  For nonnegative values, `gamma^n value` is monotone in gamma.  Therefore an
  exact envelope with gamma <= 1/2 is pointwise below the established half-power
  envelope and inherits its identity-modulus signed rate-null certificate.
  Exact paired-trajectory and successive-residual bounds can then be promoted
  directly to rate-null results without discarding the sharper finite-horizon
  estimates.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-nnrat-exact-rate :as exact]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
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
(defn- power-scale [gamma steps value]
  (app (function/const* 'signed/nnrat-power-scale [])
       gamma steps value))
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null [])
       sequence modulus))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- row-sums-bounded [rows gamma]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) (from-nnrat gamma))))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- rate-nonnegative [gamma]
  (app (function/const* 'signed/zero-at-most-from-nnrat []) gamma))

(def nnrat-power-scale-rate-monotone-spec
  {:name 'signed/nnrat-power-scale-rate-monotone :universes []
   :type
   (function/forall
    [['gamma nnrat] ['delta nnrat]
     ['gamma-at-most-delta (rle 'gamma 'delta)]
     ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (sle (power-scale 'gamma 'steps 'value)
         (power-scale 'delta 'steps 'value)))
   :value
   (function/lam
    [['gamma nnrat] ['delta nnrat]
     ['gamma-at-most-delta (rle 'gamma 'delta)]
     ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (sle (power-scale 'gamma 'n 'value)
                (power-scale 'delta 'n 'value)))
          step
          (function/lam
           [['n nat] ['previous-ordered (app motive 'n)]]
           (let [gamma-rate (from-nnrat 'gamma)
                 delta-rate (from-nnrat 'delta)
                 gamma-previous (power-scale 'gamma 'n 'value)
                 delta-previous (power-scale 'delta 'n 'value)
                 first-bound
                 (app
                  (function/const* 'signed/multiply-left-monotone [])
                  gamma-rate gamma-previous delta-previous
                  (rate-nonnegative 'gamma) 'previous-ordered)
                 delta-previous-nonnegative
                 (app
                  (function/const*
                   'signed/nnrat-power-scale-nonnegative [])
                  'delta 'value 'value-nonnegative 'n)
                 rate-ordered
                 (app (function/const* 'signed/from-nnrat-at-most [])
                      'gamma 'delta 'gamma-at-most-delta)
                 second-bound
                 (app
                  (function/const* 'signed/multiply-right-monotone [])
                  delta-previous gamma-rate delta-rate
                  delta-previous-nonnegative rate-ordered)]
             (order-transitive
              (smul gamma-rate gamma-previous)
              (smul gamma-rate delta-previous)
              (smul delta-rate delta-previous)
              first-bound second-bound)))]
      (prop-nat-rec
       motive
       (app (function/const* 'signed/at-most-reflexive []) 'value)
       step 'steps)))})

(def nnrat-power-scale-at-most-half-power-spec
  {:name 'signed/nnrat-power-scale-at-most-half-power :universes []
   :type
   (function/forall
    [['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (sle (power-scale 'gamma 'steps 'value)
         (half-power-scale 'steps 'value)))
   :value
   (function/lam
    [['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['steps nat]]
    (app
     (function/const* 'signed/nnrat-power-scale-rate-monotone [])
     'gamma nnrat-half 'gamma-at-most-half
     'value 'value-nonnegative 'steps))})

(def signed-nnrat-power-rate-null-spec
  (let [exact-sequence
        (function/lam
         [['n nat]] (power-scale 'gamma 'n 'value))
        half-sequence
        (function/lam
         [['n nat]] (half-power-scale 'n 'value))
        modulus (function/lam [['k nat]] 'k)]
    {:name 'analysis/signed-nnrat-power-rate-null-of-at-most-half
     :universes []
     :type
     (function/forall
      [['gamma nnrat]
       ['gamma-at-most-half (rle 'gamma nnrat-half)]
       ['value signed]
       ['value-nonnegative (sle signed-zero 'value)]
       ['value-at-most-one (sle 'value signed-one)]]
      (signed-rate-null exact-sequence modulus))
     :value
     (function/lam
      [['gamma nnrat]
       ['gamma-at-most-half (rle 'gamma nnrat-half)]
       ['value signed]
       ['value-nonnegative (sle signed-zero 'value)]
       ['value-at-most-one (sle 'value signed-one)]]
      (app
       (function/const* 'analysis/signed-rate-null-dominated [])
       half-sequence exact-sequence modulus
       (function/lam
        [['n nat]]
        (app
         (function/const* 'signed/nnrat-power-scale-nonnegative [])
         'gamma 'value 'value-nonnegative 'n))
       (function/lam
        [['n nat]]
        (app
         (function/const*
          'signed/nnrat-power-scale-at-most-half-power [])
         'gamma 'gamma-at-most-half
         'value 'value-nonnegative 'n))
       (app
        (function/const*
         'analysis/signed-half-power-rate-null-of-at-most-one [])
        'value 'value-nonnegative 'value-at-most-one)))}))

(defn- paired-null-binders []
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] ['right vector-type]
   ['gamma nnrat]
   ['gamma-at-most-half (rle 'gamma nnrat-half)]
   ['shape (same-shape 'left 'right)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (row-sums-bounded 'rows 'gamma)]
   ['initial-distance-at-most-one
    (sle (sup-distance 'left 'right) signed-one)]])

(def affine-nnrat-paired-rate-null-spec
  (let [initial-distance (sup-distance 'left 'right)
        envelope
        (function/lam
         [['n nat]] (power-scale 'gamma 'n initial-distance))
        error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          (affine-iterate 'rows 'offset 'n 'right)))
        modulus (function/lam [['k nat]] 'k)]
    {:name 'matrix/affine-nnrat-iterate-sup-distance-rate-null-exact-envelope
     :universes []
     :type
     (function/forall
      (paired-null-binders)
      (signed-rate-null error modulus))
     :value
     (function/lam
      (paired-null-binders)
      (let [distance-nonnegative
            (app (function/const* 'vector/sup-distance-nonnegative [])
                 'left 'right)
            envelope-null
            (app
             (function/const*
              'analysis/signed-nnrat-power-rate-null-of-at-most-half [])
             'gamma 'gamma-at-most-half initial-distance
             distance-nonnegative 'initial-distance-at-most-one)]
        (app
         (function/const* 'analysis/signed-rate-null-dominated [])
         envelope error modulus
         (function/lam
          [['n nat]]
          (app (function/const* 'vector/sup-distance-nonnegative [])
               (affine-iterate 'rows 'offset 'n 'left)
               (affine-iterate 'rows 'offset 'n 'right)))
         (function/lam
          [['n nat]]
          (app
           (function/const*
            'matrix/affine-nnrat-row-sum-iterate-sup-distance-rate [])
           'rows 'offset 'left 'right 'gamma
           'shape 'offset-shape 'positive-rows 'bounded-sums 'n))
         envelope-null)))}))

(defn- residual-null-binders []
  (let [first-image (affine-action 'rows 'offset 'initial)]
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['gamma nnrat]
     ['gamma-at-most-half (rle 'gamma nnrat-half)]
     ['step-shape (same-shape 'initial first-image)]
     ['offset-shape (same-shape 'offset (action 'rows 'initial))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (row-sums-bounded 'rows 'gamma)]
     ['initial-residual-at-most-one
      (sle (sup-distance 'initial first-image) signed-one)]]))

(def affine-nnrat-residual-rate-null-spec
  (let [first-image (affine-action 'rows 'offset 'initial)
        initial-residual (sup-distance 'initial first-image)
        envelope
        (function/lam
         [['n nat]] (power-scale 'gamma 'n initial-residual))
        error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'initial)
          (affine-iterate 'rows 'offset
                          (app (function/const* 'data/succ []) 'n)
                          'initial)))
        modulus (function/lam [['k nat]] 'k)]
    {:name 'matrix/affine-nnrat-successive-residual-rate-null-exact-envelope
     :universes []
     :type
     (function/forall
      (residual-null-binders)
      (signed-rate-null error modulus))
     :value
     (function/lam
      (residual-null-binders)
      (let [residual-nonnegative
            (app (function/const* 'vector/sup-distance-nonnegative [])
                 'initial first-image)
            envelope-null
            (app
             (function/const*
              'analysis/signed-nnrat-power-rate-null-of-at-most-half [])
             'gamma 'gamma-at-most-half initial-residual
             residual-nonnegative 'initial-residual-at-most-one)]
        (app
         (function/const* 'analysis/signed-rate-null-dominated [])
         envelope error modulus
         (function/lam
          [['n nat]]
          (app
           (function/const* 'vector/sup-distance-nonnegative [])
           (affine-iterate 'rows 'offset 'n 'initial)
           (affine-iterate 'rows 'offset
                           (app (function/const* 'data/succ []) 'n)
                           'initial)))
         (function/lam
          [['n nat]]
          (app
           (function/const*
            'matrix/affine-nnrat-successive-residual-rate [])
           'rows 'offset 'initial 'gamma
           'step-shape 'offset-shape
           'positive-rows 'bounded-sums 'n))
         envelope-null)))}))

(def definition-specs [])
(def theorem-specs
  [nnrat-power-scale-rate-monotone-spec
   nnrat-power-scale-at-most-half-power-spec
   signed-nnrat-power-rate-null-spec
   affine-nnrat-paired-rate-null-spec
   affine-nnrat-residual-rate-null-spec])

(defn extend-environment [env]
  (-> env
      exact/extend-environment
      (support/extend-with
       :finite-matrix-affine-nnrat-exact-rate-null theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
