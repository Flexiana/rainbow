(ns rainbow.math.linear.matrix.affine-approximate-fixed-point
  "Constructive approximate fixed points from affine residual convergence.

  Exact signed-rational affine contraction need not be accompanied by a supplied
  fixed point.  The exact-envelope residual-null theorem nevertheless produces
  an explicit approximate one: at every reciprocal tolerance index k, the kth
  iterate has residual at most `from-nnrat(harmonic k)`, and every later iterate
  satisfies the same bound.  The existential theorem packages that iterate as
  proof data rather than merely asserting asymptotic behavior.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.affine-nnrat-exact-rate-null
             :as exact-null]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def signed-sequence (function/arrow nat signed))
(def nat-modulus (function/arrow nat nat))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
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
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null [])
       sequence modulus))
(defn- harmonic-radius [index]
  (from-nnrat
   (app (function/const* 'nnrat/harmonic []) index)))
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
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def signed-rate-null-at-modulus-spec
  {:name 'analysis/signed-rate-null-at-modulus :universes []
   :type
   (function/forall
    [['sequence signed-sequence] ['modulus nat-modulus]
     ['null (signed-rate-null 'sequence 'modulus)]
     ['index nat]]
    (let [value (app 'sequence (app 'modulus 'index))
          radius (harmonic-radius 'index)]
      (conjunction (sle signed-zero value)
                   (sle value radius))))
   :value
   (function/lam
    [['sequence signed-sequence] ['modulus nat-modulus]
     ['null (signed-rate-null 'sequence 'modulus)]
     ['index nat]]
    (app
     'null 'index (app 'modulus 'index)
     (app (function/const* 'nat/at-most-reflexive [])
          (app 'modulus 'index))))})

(defn- approximation-binders [include-horizon?]
  (let [first-image (affine-action 'rows 'offset 'initial)
        base
        [['rows matrix-type] ['offset vector-type] ['initial vector-type]
         ['gamma nnrat]
         ['gamma-at-most-half (rle 'gamma nnrat-half)]
         ['step-shape (same-shape 'initial first-image)]
         ['offset-shape (same-shape 'offset (action 'rows 'initial))]
         ['positive-rows (rows-positive 'rows)]
         ['bounded-sums (row-sums-bounded 'rows 'gamma)]
         ['initial-residual-at-most-one
          (sle (sup-distance 'initial first-image) signed-one)]]]
    (if include-horizon?
      (into base
            [['index nat] ['steps nat]
             ['large-enough (nat-at-most 'index 'steps)]])
      (conj base ['index nat]))))

(def affine-eventually-approximate-fixed-point-spec
  (let [current (affine-iterate 'rows 'offset 'steps 'initial)
        successor-current
        (affine-iterate 'rows 'offset (succ 'steps) 'initial)
        successive-residual
        (sup-distance current successor-current)
        computable-residual
        (sup-distance current (affine-action 'rows 'offset current))
        radius (harmonic-radius 'index)
        residual-sequence
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'initial)
          (affine-iterate 'rows 'offset (succ 'n) 'initial)))]
    {:name 'matrix/affine-nnrat-eventually-approximate-fixed-point
     :universes []
     :type
     (function/forall
      (approximation-binders true)
      (sle computable-residual radius))
     :value
     (function/lam
      (approximation-binders true)
      (let [residual-null
            (app
             (function/const*
              'matrix/affine-nnrat-successive-residual-rate-null-exact-envelope [])
             'rows 'offset 'initial 'gamma 'gamma-at-most-half
             'step-shape 'offset-shape
             'positive-rows 'bounded-sums
             'initial-residual-at-most-one)
            bounds
            (app residual-null 'index 'steps 'large-enough)
            successive-upper
            (proposition-right
             (sle signed-zero successive-residual)
             (sle successive-residual radius)
             bounds)
            successor-unfold
            (app (function/const* 'matrix/affine-iterate-successor [])
                 'rows 'offset 'steps 'initial)
            residual-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             current successor-current
             (affine-action 'rows 'offset current)
             successor-unfold)]
        (order-respects
         successive-residual computable-residual radius radius
         residual-same (signed-reflexive radius)
         successive-upper)))}))

(def affine-approximate-fixed-point-at-horizon-spec
  (let [current (affine-iterate 'rows 'offset 'index 'initial)]
    {:name 'matrix/affine-nnrat-approximate-fixed-point-at-horizon
     :universes []
     :type
     (function/forall
      (approximation-binders false)
      (sle
       (sup-distance current (affine-action 'rows 'offset current))
       (harmonic-radius 'index)))
     :value
     (function/lam
      (approximation-binders false)
      (app
       (function/const*
        'matrix/affine-nnrat-eventually-approximate-fixed-point [])
       'rows 'offset 'initial 'gamma 'gamma-at-most-half
       'step-shape 'offset-shape
       'positive-rows 'bounded-sums
       'initial-residual-at-most-one
       'index 'index
       (app (function/const* 'nat/at-most-reflexive []) 'index)))}))

(def affine-approximate-fixed-point-exists-spec
  (let [predicate
        (function/lam
         [['approximate vector-type]]
         (sle
          (sup-distance
           'approximate (affine-action 'rows 'offset 'approximate))
          (harmonic-radius 'index)))
        witness-value
        (affine-iterate 'rows 'offset 'index 'initial)]
    {:name 'matrix/affine-nnrat-approximate-fixed-point-exists
     :universes []
     :type
     (function/forall
      (approximation-binders false)
      (proposition/existence type-level vector-type predicate))
     :value
     (function/lam
      (approximation-binders false)
      (app
       (function/const* 'proposition/witness [type-level])
       vector-type predicate witness-value
       (app
        (function/const*
         'matrix/affine-nnrat-approximate-fixed-point-at-horizon [])
        'rows 'offset 'initial 'gamma 'gamma-at-most-half
        'step-shape 'offset-shape
        'positive-rows 'bounded-sums
        'initial-residual-at-most-one 'index)))}))

(def definition-specs [])
(def theorem-specs
  [signed-rate-null-at-modulus-spec
   affine-eventually-approximate-fixed-point-spec
   affine-approximate-fixed-point-at-horizon-spec
   affine-approximate-fixed-point-exists-spec])

(defn extend-environment [env]
  (-> env
      exact-null/extend-environment
      (support/extend-with
       :finite-matrix-affine-approximate-fixed-point theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
