(ns rainbow.math.finite.bellman-signed-policy-approximate-fixed-point
  "Constructive approximate fixed points for finite signed policy evaluation.

  The signed fixed-policy Bellman operator is an affine map on an explicit
  vector.  For nonnegative rows whose sums are bounded by gamma <= 1/2, and an
  initial residual at most one, its kth iterate is an independently checkable
  approximate fixed point with residual at most 1/(k+1).  The existential
  theorem exposes that computed iterate as proof data.

  This removes the exact-fixed-point premise from finite-tolerance policy
  evaluation.  It does not construct an exact rational fixed point: the latter
  remains a separate algebraic existence obligation.  Native, kernel-checked,
  and axiom-free on D63."
  (:require [rainbow.math.finite.bellman-signed-policy :as policy]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
             :as general-convergence]
            [rainbow.math.linear.matrix.affine-approximate-fixed-point
             :as approximate]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
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
(defn- succ [value] (app successor value))
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nmul [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
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
(defn- policy-step [rows reward values]
  (app (function/const* 'bellman/signed-policy-step [])
       rows reward values))
(defn- policy-iterate [rows reward steps initial]
  (app (function/const* 'bellman/signed-policy-iterate [])
       rows reward steps initial))
(defn- harmonic-radius [index]
  (from-nnrat (app (function/const* 'nnrat/harmonic []) index)))
(defn- general-harmonic-radius [ap gp steps]
  (from-nnrat
   (app (function/const* 'nnrat/general-harmonic []) ap gp steps)))
(defn- power-scale [gamma steps value]
  (app (function/const* 'signed/nnrat-power-scale [])
       gamma steps value))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null []) sequence modulus))
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
(defn- order-respects
  [left left-prime right right-prime left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime left-same right-same ordered))
(defn- signed-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(defn- approximation-binders [include-steps?]
  (let [first-image (policy-step 'rows 'reward 'initial)
        base
        [['rows matrix-type] ['reward vector-type] ['initial vector-type]
         ['gamma nnrat]
         ['gamma-at-most-half (rle 'gamma nnrat-half)]
         ['step-shape (same-shape 'initial first-image)]
         ['reward-shape (same-shape 'reward (action 'rows 'initial))]
         ['positive-rows (rows-positive 'rows)]
         ['bounded-sums (row-sums-bounded 'rows 'gamma)]
         ['initial-residual-at-most-one
          (sle (sup-distance 'initial first-image) signed-one)]]]
    (if include-steps?
      (into base
            [['index nat] ['steps nat]
             ['large-enough
              (app (function/const* 'nat/at-most []) 'index 'steps)]])
      (conj base ['index nat]))))

(def signed-policy-eventually-approximate-fixed-point-spec
  (let [current (policy-iterate 'rows 'reward 'steps 'initial)]
    {:name 'bellman/signed-policy-eventually-approximate-fixed-point
     :universes []
     :type
     (function/forall
      (approximation-binders true)
      (sle
       (sup-distance current (policy-step 'rows 'reward current))
       (harmonic-radius 'index)))
     :value
     (function/lam
      (approximation-binders true)
      (app
       (function/const*
        'matrix/affine-nnrat-eventually-approximate-fixed-point [])
       'rows 'reward 'initial 'gamma 'gamma-at-most-half
       'step-shape 'reward-shape 'positive-rows 'bounded-sums
       'initial-residual-at-most-one 'index 'steps 'large-enough))}))

(def signed-policy-approximate-fixed-point-at-horizon-spec
  (let [current (policy-iterate 'rows 'reward 'index 'initial)]
    {:name 'bellman/signed-policy-approximate-fixed-point-at-horizon
     :universes []
     :type
     (function/forall
      (approximation-binders false)
      (sle
       (sup-distance current (policy-step 'rows 'reward current))
       (harmonic-radius 'index)))
     :value
     (function/lam
      (approximation-binders false)
      (app
       (function/const*
        'matrix/affine-nnrat-approximate-fixed-point-at-horizon [])
       'rows 'reward 'initial 'gamma 'gamma-at-most-half
       'step-shape 'reward-shape 'positive-rows 'bounded-sums
       'initial-residual-at-most-one 'index))}))

(def signed-policy-approximate-fixed-point-exists-spec
  (let [predicate
        (function/lam
         [['candidate vector-type]]
         (sle
          (sup-distance
           'candidate (policy-step 'rows 'reward 'candidate))
          (harmonic-radius 'index)))]
    {:name 'bellman/signed-policy-approximate-fixed-point-exists
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
       vector-type predicate
       (policy-iterate 'rows 'reward 'index 'initial)
       (app
        (function/const*
         'bellman/signed-policy-approximate-fixed-point-at-horizon [])
        'rows 'reward 'initial 'gamma 'gamma-at-most-half
        'step-shape 'reward-shape 'positive-rows 'bounded-sums
        'initial-residual-at-most-one 'index)))}))

(defn- general-rate-binders [include-index?]
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        first-image (policy-step 'rows 'reward 'initial)
        initial-residual (sup-distance 'initial first-image)
        base
        [['ap nat] ['gp nat]
         ['rows matrix-type] ['reward vector-type] ['initial vector-type]
         ['step-shape (same-shape 'initial first-image)]
         ['reward-shape (same-shape 'reward (action 'rows 'initial))]
         ['positive-rows (rows-positive 'rows)]
         ['bounded-sums (row-sums-bounded 'rows gamma)]
         ['initial-bound
          (sle initial-residual
               (general-harmonic-radius 'ap 'gp nat-zero))]]]
    (if include-index? (conj base ['index nat]) base)))

(def signed-policy-successive-residual-rate-null-general-spec
  (let [gamma (rmake (succ 'ap) (nadd 'ap (succ 'gp)))
        initial-image (policy-step 'rows 'reward 'initial)
        initial-residual (sup-distance 'initial initial-image)
        envelope
        (function/lam
         [['steps nat]] (power-scale gamma 'steps initial-residual))
        residual
        (function/lam
         [['steps nat]]
         (sup-distance
          (policy-iterate 'rows 'reward 'steps 'initial)
          (policy-iterate 'rows 'reward (succ 'steps) 'initial)))
        modulus
        (function/lam
         [['index nat]] (nmul (succ 'ap) 'index))]
    {:name 'bellman/signed-policy-successive-residual-rate-null-general
     :universes []
     :type
     (function/forall
      (general-rate-binders false)
      (signed-rate-null residual modulus))
     :value
     (function/lam
      (general-rate-binders false)
      (let [initial-residual-nonnegative
            (app (function/const* 'vector/sup-distance-nonnegative [])
                 'initial initial-image)
            envelope-null
            (app
             (function/const*
              'analysis/signed-nnrat-power-rate-null-general [])
             'ap 'gp initial-residual
             initial-residual-nonnegative 'initial-bound)]
        (app
         (function/const* 'analysis/signed-rate-null-dominated [])
         envelope residual modulus
         (function/lam
          [['steps nat]]
          (app (function/const* 'vector/sup-distance-nonnegative [])
               (policy-iterate 'rows 'reward 'steps 'initial)
               (policy-iterate 'rows 'reward (succ 'steps) 'initial)))
         (function/lam
          [['steps nat]]
          (app
           (function/const*
            'matrix/affine-nnrat-successive-residual-rate [])
           'rows 'reward 'initial gamma
           'step-shape 'reward-shape
           'positive-rows 'bounded-sums 'steps))
         envelope-null)))}))

(def signed-policy-approximate-fixed-point-general-rate-spec
  (let [steps (nmul (succ 'ap) 'index)
        current (policy-iterate 'rows 'reward steps 'initial)
        successor-current
        (policy-iterate 'rows 'reward (succ steps) 'initial)
        successive-residual (sup-distance current successor-current)
        computable-residual
        (sup-distance current (policy-step 'rows 'reward current))
        radius (harmonic-radius 'index)]
    {:name 'bellman/signed-policy-approximate-fixed-point-general-rate
     :universes []
     :type
     (function/forall
      (general-rate-binders true)
      (sle computable-residual radius))
     :value
     (function/lam
      (general-rate-binders true)
      (let [residual-null
            (app
             (function/const*
              'bellman/signed-policy-successive-residual-rate-null-general [])
             'ap 'gp 'rows 'reward 'initial
             'step-shape 'reward-shape
             'positive-rows 'bounded-sums 'initial-bound)
            residual-bounds
            (app residual-null 'index steps
                 (app (function/const* 'nat/at-most-reflexive []) steps))
            successive-upper
            (proposition-right
             (sle signed-zero successive-residual)
             (sle successive-residual radius)
             residual-bounds)
            successor-unfold
            (app (function/const* 'matrix/affine-iterate-successor [])
                 'rows 'reward steps 'initial)
            residual-same
            (app
             (function/const*
              'vector/sup-distance-right-respects-equivalence [])
             current successor-current
             (policy-step 'rows 'reward current)
             successor-unfold)]
        (order-respects
         successive-residual computable-residual radius radius
         residual-same (signed-reflexive radius) successive-upper)))}))

(def signed-policy-approximate-fixed-point-exists-general-rate-spec
  (let [steps (nmul (succ 'ap) 'index)
        predicate
        (function/lam
         [['candidate vector-type]]
         (sle
          (sup-distance
           'candidate (policy-step 'rows 'reward 'candidate))
          (harmonic-radius 'index)))]
    {:name 'bellman/signed-policy-approximate-fixed-point-exists-general-rate
     :universes []
     :type
     (function/forall
      (general-rate-binders true)
      (proposition/existence type-level vector-type predicate))
     :value
     (function/lam
      (general-rate-binders true)
      (app
       (function/const* 'proposition/witness [type-level])
       vector-type predicate
       (policy-iterate 'rows 'reward steps 'initial)
       (app
        (function/const*
         'bellman/signed-policy-approximate-fixed-point-general-rate [])
        'ap 'gp 'rows 'reward 'initial
        'step-shape 'reward-shape
        'positive-rows 'bounded-sums 'initial-bound 'index)))}))

(def definition-specs [])
(def theorem-specs
  [signed-policy-eventually-approximate-fixed-point-spec
   signed-policy-approximate-fixed-point-at-horizon-spec
   signed-policy-approximate-fixed-point-exists-spec
   signed-policy-successive-residual-rate-null-general-spec
   signed-policy-approximate-fixed-point-general-rate-spec
   signed-policy-approximate-fixed-point-exists-general-rate-spec])

(defn extend-environment [env]
  (-> env
      approximate/extend-environment
      policy/extend-environment
      general-convergence/extend-environment
      (support/extend-with
       :finite-bellman-signed-policy-approximate-fixed-point theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
