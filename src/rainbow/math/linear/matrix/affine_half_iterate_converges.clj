(ns rainbow.math.linear.matrix.affine-half-iterate-converges
  "Rate-null convergence for half-row signed affine iteration.

  The older `analysis/converges` quantifies over negative signed radii and is
  intentionally documented as uninhabitable even by constant sequences.  This
  module instead defines `analysis/signed-rate-null` over the constructive
  reciprocal NNRAT ladder: after modulus M(k), a signed sequence is nonnegative
  and at most the embedded radius 1/(k+1).  Domination and pointwise signed
  equivalence preserve this certificate.

  The signed geometric bridge proves the half-power unit envelope rate-null.
  Consequently unit-bounded paired affine iterates coalesce at that rate, and
  iteration from any unit-bounded initial distance converges to a certified
  fixed point.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-equivalence :as affine-equivalence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.geometric-convergence :as geometric]
            [rainbow.math.rational.nnrat.harmonic-convergence :as harmonic]
            [rainbow.math.rational.signed.geometric-bridge :as bridge]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def signed-sequence (function/arrow nat signed))
(def nat-modulus (function/arrow nat nat))

(defn- app [f & xs] (apply function/app f xs))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- harmonic-radius [index]
  (from-nnrat
   (app (function/const* 'nnrat/harmonic []) index)))
(defn- half-power-scale [steps value]
  (app (function/const* 'signed/half-power-scale []) steps value))
(defn- signed-rate-null [sequence modulus]
  (app (function/const* 'analysis/signed-rate-null [])
       sequence modulus))
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
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(def signed-half
  (from-nnrat (function/const* 'nnrat/half [])))
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
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       left-same right-same ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       left-same right-same ordered))

(def signed-rate-null-spec
  {:name 'analysis/signed-rate-null :kind :definition :universes []
   :type (function/arrow signed-sequence nat-modulus 'Prop)
   :value
   (function/lam
    [['sequence signed-sequence] ['modulus nat-modulus]]
    (function/forall
     [['k nat] ['n nat]
      ['large-enough
       (nat-at-most (app 'modulus 'k) 'n)]]
     (let [value (app 'sequence 'n)
           radius (harmonic-radius 'k)]
       (conjunction
        (sle signed-zero value)
        (sle value radius)))))})

(def signed-half-power-one-rate-null-spec
  {:name 'analysis/signed-half-power-one-rate-null :universes []
   :type
   (signed-rate-null
    (function/lam [['n nat]] (half-power-scale 'n signed-one))
    (function/lam [['k nat]] 'k))
   :value
   (function/lam
    [['k nat] ['n nat]
     ['large-enough (nat-at-most 'k 'n)]]
    (let [power (half-power-scale 'n signed-one)
          geometric-value
          (app (function/const* 'nnrat/geometric-half []) 'n)
          embedded-geometric (from-nnrat geometric-value)
          radius (harmonic-radius 'k)
          power-nonnegative
          (app (function/const* 'signed/half-power-scale-nonnegative [])
               signed-one
               (function/const* 'signed/zero-at-most-one [])
               'n)
          geometric-bound
          (app (function/const* 'analysis/geometric-half-rate-null [])
               'k 'n 'large-enough)
          embedded-bound
          (app (function/const* 'signed/from-nnrat-at-most [])
               geometric-value
               (app (function/const* 'nnrat/harmonic []) 'k)
               geometric-bound)
          power-geometric
          (app (function/const* 'signed/half-power-one-geometric [])
               'n)
          power-bound
          (order-respects
           embedded-geometric power radius radius
           (app (function/const* 'signed/equivalent-symmetric [])
                power embedded-geometric power-geometric)
           (app (function/const* 'signed/equivalent-reflexive [])
                radius)
           embedded-bound)]
      (conjoin
       (sle signed-zero power) (sle power radius)
       power-nonnegative power-bound)))})

(def signed-rate-null-dominated-spec
  {:name 'analysis/signed-rate-null-dominated :universes []
   :type
   (function/forall
    [['source signed-sequence] ['target signed-sequence]
     ['modulus nat-modulus]
     ['target-nonnegative
      (function/forall
       [['n nat]] (sle signed-zero (app 'target 'n)))]
     ['dominated
      (function/forall
       [['n nat]] (sle (app 'target 'n) (app 'source 'n)))]
     ['source-null (signed-rate-null 'source 'modulus)]]
    (signed-rate-null 'target 'modulus))
   :value
   (function/lam
    [['source signed-sequence] ['target signed-sequence]
     ['modulus nat-modulus]
     ['target-nonnegative
      (function/forall
       [['n nat]] (sle signed-zero (app 'target 'n)))]
     ['dominated
      (function/forall
       [['n nat]] (sle (app 'target 'n) (app 'source 'n)))]
     ['source-null (signed-rate-null 'source 'modulus)]]
    (function/lam
     [['k nat] ['n nat]
      ['large-enough
       (nat-at-most (app 'modulus 'k) 'n)]]
     (let [source-value (app 'source 'n)
           target-value (app 'target 'n)
           radius (harmonic-radius 'k)
           source-bounds
           (app 'source-null 'k 'n 'large-enough)
           source-upper
           (proposition-right
            (sle signed-zero source-value)
            (sle source-value radius)
            source-bounds)
           target-upper
           (order-transitive
            target-value source-value radius
            (app 'dominated 'n) source-upper)]
       (conjoin
        (sle signed-zero target-value)
        (sle target-value radius)
        (app 'target-nonnegative 'n) target-upper))))})

(def signed-rate-null-respects-equivalence-spec
  {:name 'analysis/signed-rate-null-respects-equivalence :universes []
   :type
   (function/forall
    [['source signed-sequence] ['target signed-sequence]
     ['modulus nat-modulus]
     ['pointwise
      (function/forall
       [['n nat]] (veq (app 'source 'n) (app 'target 'n)))]
     ['source-null (signed-rate-null 'source 'modulus)]]
    (signed-rate-null 'target 'modulus))
   :value
   (function/lam
    [['source signed-sequence] ['target signed-sequence]
     ['modulus nat-modulus]
     ['pointwise
      (function/forall
       [['n nat]] (veq (app 'source 'n) (app 'target 'n)))]
     ['source-null (signed-rate-null 'source 'modulus)]]
    (function/lam
     [['k nat] ['n nat]
      ['large-enough
       (nat-at-most (app 'modulus 'k) 'n)]]
     (let [source-value (app 'source 'n)
           target-value (app 'target 'n)
           radius (harmonic-radius 'k)
           source-bounds
           (app 'source-null 'k 'n 'large-enough)
           source-nonnegative
           (proposition-left
            (sle signed-zero source-value)
            (sle source-value radius)
            source-bounds)
           source-upper
           (proposition-right
            (sle signed-zero source-value)
            (sle source-value radius)
            source-bounds)
           same (app 'pointwise 'n)
           target-nonnegative
           (order-respects
            signed-zero signed-zero source-value target-value
            (app (function/const* 'signed/equivalent-reflexive [])
                 signed-zero)
            same source-nonnegative)
           target-upper
           (order-respects
            source-value target-value radius radius
            same
            (app (function/const* 'signed/equivalent-reflexive [])
                 radius)
            source-upper)]
       (conjoin
        (sle signed-zero target-value)
        (sle target-value radius)
        target-nonnegative target-upper))))})

(def signed-half-power-rate-null-of-at-most-one-spec
  {:name 'analysis/signed-half-power-rate-null-of-at-most-one :universes []
   :type
   (function/forall
    [['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['value-at-most-one (sle 'value signed-one)]]
    (signed-rate-null
     (function/lam [['n nat]] (half-power-scale 'n 'value))
     (function/lam [['k nat]] 'k)))
   :value
   (function/lam
    [['value signed]
     ['value-nonnegative (sle signed-zero 'value)]
     ['value-at-most-one (sle 'value signed-one)]]
    (let [source
          (function/lam
           [['n nat]] (half-power-scale 'n signed-one))
          target
          (function/lam
           [['n nat]] (half-power-scale 'n 'value))]
      (app
       (function/const* 'analysis/signed-rate-null-dominated [])
       source target (function/lam [['k nat]] 'k)
       (function/lam
        [['n nat]]
        (app
         (function/const* 'signed/half-power-scale-nonnegative [])
         'value 'value-nonnegative 'n))
       (function/lam
        [['n nat]]
        (app
         (function/const* 'signed/half-power-scale-monotone [])
         'value signed-one 'value-at-most-one 'n))
       (function/const*
        'analysis/signed-half-power-one-rate-null []))))})

(defn- affine-rate-binders [right-name]
  [['rows matrix-type] ['offset vector-type]
   ['left vector-type] [right-name vector-type]
   ['initial-shape (same-shape 'left right-name)]
   ['offset-shape (same-shape 'offset (action 'rows 'left))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums (half-row-sums 'rows)]
   ['initial-distance-at-most-one
    (sle (sup-distance 'left right-name) signed-one)]])

(def affine-half-iterate-sup-distance-rate-null-spec
  (let [binders (affine-rate-binders 'right)
        error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          (affine-iterate 'rows 'offset 'n 'right)))]
    {:name 'matrix/affine-half-iterate-sup-distance-rate-null
     :universes []
     :type
     (function/forall
      binders
      (signed-rate-null error (function/lam [['k nat]] 'k)))
     :value
     (function/lam
      binders
      (let [initial-distance (sup-distance 'left 'right)
            envelope
            (function/lam
             [['n nat]] (half-power-scale 'n signed-one))]
        (app
         (function/const* 'analysis/signed-rate-null-dominated [])
         envelope error (function/lam [['k nat]] 'k)
         (function/lam
          [['n nat]]
          (app (function/const*
                'vector/sup-distance-nonnegative [])
               (affine-iterate 'rows 'offset 'n 'left)
               (affine-iterate 'rows 'offset 'n 'right)))
         (function/lam
          [['n nat]]
          (let [finite-rate
                (app
                 (function/const*
                  'matrix/affine-half-iterate-sup-distance-rate [])
                 'rows 'offset 'left 'right
                 'initial-shape 'offset-shape
                 'positive-rows 'bounded-sums 'n)
                envelope-monotone
                (app
                 (function/const*
                  'signed/half-power-scale-monotone [])
                 initial-distance signed-one
                 'initial-distance-at-most-one 'n)]
            (order-transitive
             (app error 'n)
             (half-power-scale 'n initial-distance)
             (app envelope 'n)
             finite-rate envelope-monotone)))
         (function/const*
          'analysis/signed-half-power-one-rate-null []))))}))

(def affine-half-iterate-converges-to-fixed-point-spec
  (let [binders
        (conj (affine-rate-binders 'fixed-point)
              ['fixed
               (vector-equivalent
                (affine-action 'rows 'offset 'fixed-point)
                'fixed-point)])
        paired-error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          (affine-iterate 'rows 'offset 'n 'fixed-point)))
        fixed-error
        (function/lam
         [['n nat]]
         (sup-distance
          (affine-iterate 'rows 'offset 'n 'left)
          'fixed-point))]
    {:name 'matrix/affine-half-iterate-converges-to-fixed-point
     :universes []
     :type
     (function/forall
      binders
      (signed-rate-null fixed-error (function/lam [['k nat]] 'k)))
     :value
     (function/lam
      binders
      (let [paired-null
            (app
             (function/const*
              'matrix/affine-half-iterate-sup-distance-rate-null [])
             'rows 'offset 'left 'fixed-point
             'initial-shape 'offset-shape
             'positive-rows 'bounded-sums
             'initial-distance-at-most-one)
            pointwise
            (function/lam
             [['n nat]]
             (app
              (function/const*
               'vector/sup-distance-right-respects-equivalence [])
              (affine-iterate 'rows 'offset 'n 'left)
              (affine-iterate 'rows 'offset 'n 'fixed-point)
              'fixed-point
              (app
               (function/const* 'matrix/affine-iterate-fixed-point [])
               'rows 'offset 'fixed-point 'fixed 'n)))]
        (app
         (function/const*
          'analysis/signed-rate-null-respects-equivalence [])
         paired-error fixed-error
         (function/lam [['k nat]] 'k)
         pointwise paired-null)))}))

(def definition-specs [signed-rate-null-spec])
(def theorem-specs
  [signed-half-power-one-rate-null-spec
   signed-rate-null-dominated-spec
   signed-rate-null-respects-equivalence-spec
   signed-half-power-rate-null-of-at-most-one-spec
   affine-half-iterate-sup-distance-rate-null-spec
   affine-half-iterate-converges-to-fixed-point-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(defn extend-environment [env]
  (-> env
      bridge/extend-environment
      (extend-specs-if-missing
       :nnrat-harmonic-convergence
       (concat harmonic/definition-specs harmonic/theorem-specs))
      (extend-spec-if-missing
       'nat/index-le-pow2-pred :nnrat-geometric-convergence
       geometric/index-le-pow2-pred-spec)
      (extend-spec-if-missing
       'analysis/geometric-below-harmonic :nnrat-geometric-convergence
       geometric/geometric-below-harmonic-spec)
      (extend-spec-if-missing
       'analysis/geometric-half-rate-null :nnrat-geometric-convergence
       geometric/geometric-rate-null-spec)
      (extend-spec-if-missing
       'matrix/affine-action-respects-values-equivalence
       :finite-matrix-affine-equivalence
       affine-equivalence/affine-action-respects-values-equivalence-spec)
      (extend-spec-if-missing
       'matrix/affine-iterate-fixed-point
       :finite-matrix-affine-equivalence
       affine-equivalence/affine-iterate-fixed-point-spec)
      (support/extend-with
       :finite-matrix-affine-half-iterate-converges
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
