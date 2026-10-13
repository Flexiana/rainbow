(ns rainbow.math.linear.matrix.affine-general-rate-certificate
  "Sharp affine residual certificates for every canonical rational rate below one.

  For `a = ap+1` and `g = gp+1`, the existing arbitrary-rate contraction
  development represents

      gamma = a/(a+g).

  This module constructs quotient-safe witnesses for

      gap     = g/(a+g),       gamma + gap ~ 1
      inverse = (a+g)/g,       inverse * gap ~ 1,

  transports them through `signed/from-nnrat`, and instantiates the generic
  inverse-gap residual theorem.  Consequently an affine solver whose row sums
  are bounded by gamma gets the sharp a-posteriori certificate

      d(x,x*) <= ((a+g)/g) * d(x,Fx)

  for every rational contraction rate below one, without the former
  `gamma <= 1/2` restriction and without caller-supplied quotient identities.
  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-inverse-gap-certificate
             :as inverse-gap]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.signed.geometric-bridge :as bridge]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nat-one (function/app successor nat-zero))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
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
(defn- make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- combine [left right]
  (app (function/const* 'nnrat/combine-denominator-predecessors [])
       left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
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
(defn- row-sums-bounded [rows rate]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) rate)))

(defn- rate [ap gp]
  (make (succ ap) (nadd ap (succ gp))))
(defn- gap [ap gp]
  (make (succ gp) (nadd ap (succ gp))))
(defn- inverse [ap gp]
  (make (nadd (succ ap) (succ gp)) gp))
(defn- eq-transitive [left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       nat left middle right first second))
(defn- eq-symmetric [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       nat left right same))
(defn- rat-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-add-respects [left left-prime right right-prime
                         left-same right-same]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- ring-eq [left right]
  (:proof (ring/prove-nat-eq left right)))
(defn- multiply-one-left [value]
  (eq-transitive
   (nmul nat-one value) (nmul value nat-one) value
   (app (function/const* 'nat/multiply-commutative [])
        nat-one value)
   (app (function/const* 'nat/multiply-one-right []) value)))

(def general-rate-plus-gap-spec
  {:name 'nnrat/general-rate-plus-gap :universes []
   :type
   (function/forall
    [['ap nat] ['gp nat]]
    (req (radd (rate 'ap 'gp) (gap 'ap 'gp)) nnrat-one))
   :value
   (function/lam
    [['ap nat] ['gp nat]]
    (let [a (succ 'ap)
          g (succ 'gp)
          denominator-predecessor (nadd 'ap g)
          ;; `succ (ap+g)` is definitionally `a+g`; use the latter
          ;; presentation so nat-ring sees the polynomial structure.
          denominator (nadd a g)
          sum-numerator
          (nadd (nmul a denominator) (nmul g denominator))
          combined-denominator
          (succ (combine denominator-predecessor
                         denominator-predecessor))
          left (nmul sum-numerator nat-one)
          right (nmul nat-one combined-denominator)
          left-to-sum
          (app (function/const* 'nat/multiply-one-right [])
               sum-numerator)
          sum-to-square
          (ring-eq sum-numerator (nmul denominator denominator))
          combined-to-square
          (app (function/const* 'nnrat/denominator-combine [])
               denominator-predecessor denominator-predecessor)
          left-to-combined
          (eq-transitive
           sum-numerator (nmul denominator denominator)
           combined-denominator
           sum-to-square
           (eq-symmetric
            combined-denominator (nmul denominator denominator)
            combined-to-square))
          left-to-combined
          (eq-transitive
           left sum-numerator combined-denominator
           left-to-sum left-to-combined)
          right-to-combined (multiply-one-left combined-denominator)]
      (eq-transitive
       left combined-denominator right
       left-to-combined
       (eq-symmetric right combined-denominator right-to-combined))))})

(def general-inverse-times-gap-spec
  {:name 'nnrat/general-inverse-times-gap :universes []
   :type
   (function/forall
    [['ap nat] ['gp nat]]
    (req (rmul (inverse 'ap 'gp) (gap 'ap 'gp)) nnrat-one))
   :value
   (function/lam
    [['ap nat] ['gp nat]]
    (let [a (succ 'ap)
          g (succ 'gp)
          denominator-predecessor (nadd 'ap g)
          denominator (nadd a g)
          product-numerator (nmul (nadd a g) g)
          combined-denominator
          (succ (combine 'gp denominator-predecessor))
          left (nmul product-numerator nat-one)
          right (nmul nat-one combined-denominator)
          left-to-product
          (app (function/const* 'nat/multiply-one-right [])
               product-numerator)
          product-to-denominator-product
          (ring-eq product-numerator (nmul g denominator))
          combined-to-denominator-product
          (app (function/const* 'nnrat/denominator-combine [])
               'gp denominator-predecessor)
          product-to-combined
          (eq-transitive
           product-numerator (nmul g denominator)
           combined-denominator
           product-to-denominator-product
           (eq-symmetric
            combined-denominator (nmul g denominator)
            combined-to-denominator-product))
          left-to-combined
          (eq-transitive
           left product-numerator combined-denominator
           left-to-product product-to-combined)
          right-to-combined (multiply-one-left combined-denominator)]
      (eq-transitive
       left combined-denominator right
       left-to-combined
       (eq-symmetric right combined-denominator right-to-combined))))})

(def from-nnrat-add-spec
  {:name 'signed/from-nnrat-add :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]]
    (veq
     (sadd (from-nnrat 'left) (from-nnrat 'right))
     (from-nnrat (radd 'left 'right))))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [sum (radd 'left 'right)
          negative (radd nnrat-zero nnrat-zero)
          source (radd sum nnrat-zero)
          target (radd sum negative)
          negative-zero
          (app (function/const* 'nnrat/add-zero-right []) nnrat-zero)
          target-source
          (rat-add-respects
           sum sum negative nnrat-zero
           (rat-reflexive sum) negative-zero)]
      (rat-symmetric target source target-source)))})

(def signed-general-rate-plus-gap-spec
  {:name 'signed/general-rate-plus-gap-one :universes []
   :type
   (function/forall
    [['ap nat] ['gp nat]]
    (veq
     (sadd (from-nnrat (rate 'ap 'gp))
           (from-nnrat (gap 'ap 'gp)))
     signed-one))
   :value
   (function/lam
    [['ap nat] ['gp nat]]
    (let [rate-value (rate 'ap 'gp)
          gap-value (gap 'ap 'gp)
          sum (radd rate-value gap-value)]
      (signed-transitive
       (sadd (from-nnrat rate-value) (from-nnrat gap-value))
       (from-nnrat sum) signed-one
       (app (function/const* 'signed/from-nnrat-add [])
            rate-value gap-value)
       (app
        (function/const* 'signed/from-nnrat-respects-equivalence [])
        sum nnrat-one
        (app (function/const* 'nnrat/general-rate-plus-gap [])
             'ap 'gp)))))})

(def signed-general-inverse-times-gap-spec
  {:name 'signed/general-inverse-times-gap-one :universes []
   :type
   (function/forall
    [['ap nat] ['gp nat]]
    (veq
     (smul (from-nnrat (inverse 'ap 'gp))
           (from-nnrat (gap 'ap 'gp)))
     signed-one))
   :value
   (function/lam
    [['ap nat] ['gp nat]]
    (let [inverse-value (inverse 'ap 'gp)
          gap-value (gap 'ap 'gp)
          product (rmul inverse-value gap-value)]
      (signed-transitive
       (smul (from-nnrat inverse-value) (from-nnrat gap-value))
       (from-nnrat product) signed-one
       (app (function/const* 'signed/from-nnrat-multiply [])
            inverse-value gap-value)
       (app
        (function/const* 'signed/from-nnrat-respects-equivalence [])
        product nnrat-one
        (app (function/const* 'nnrat/general-inverse-times-gap [])
             'ap 'gp)))))})

(defn- affine-binders []
  [['rows matrix-type] ['offset vector-type]
   ['approximate vector-type] ['fixed-point vector-type]
   ['ap nat] ['gp nat]
   ['shape (same-shape 'approximate 'fixed-point)]
   ['offset-shape
    (same-shape 'offset (action 'rows 'approximate))]
   ['positive-rows (rows-positive 'rows)]
   ['bounded-sums
    (row-sums-bounded 'rows (from-nnrat (rate 'ap 'gp)))]
   ['fixed
    (vector-equivalent
     (affine-action 'rows 'offset 'fixed-point)
     'fixed-point)]])

(def affine-general-rate-fixed-point-residual-bound-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)]
    {:name 'matrix/affine-general-rate-fixed-point-residual-bound
     :universes []
     :type
     (function/forall
      (affine-binders)
      (sle distance
           (smul (from-nnrat (inverse 'ap 'gp)) residual)))
     :value
     (function/lam
      (affine-binders)
      (let [rate-value (rate 'ap 'gp)
            gap-value (gap 'ap 'gp)
            inverse-value (inverse 'ap 'gp)]
        (app
         (function/const*
          'matrix/affine-inverse-gap-fixed-point-residual-bound [])
         'rows 'offset 'approximate 'fixed-point
         (from-nnrat rate-value)
         (from-nnrat gap-value)
         (from-nnrat inverse-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              rate-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              inverse-value)
         (app (function/const* 'signed/general-rate-plus-gap-one [])
              'ap 'gp)
         (app (function/const* 'signed/general-inverse-times-gap-one [])
              'ap 'gp)
         'shape 'offset-shape 'positive-rows 'bounded-sums 'fixed)))}))

(def affine-general-rate-stopping-certificate-spec
  (let [image (affine-action 'rows 'offset 'approximate)
        distance (sup-distance 'approximate 'fixed-point)
        residual (sup-distance 'approximate image)
        binders
        (into
         (affine-binders)
         [['threshold signed]
          ['residual-at-most-threshold (sle residual 'threshold)]])]
    {:name 'matrix/affine-general-rate-stopping-certificate
     :universes []
     :type
     (function/forall
      binders
      (sle distance
           (smul (from-nnrat (inverse 'ap 'gp)) 'threshold)))
     :value
     (function/lam
      binders
      (let [rate-value (rate 'ap 'gp)
            gap-value (gap 'ap 'gp)
            inverse-value (inverse 'ap 'gp)]
        (app
         (function/const* 'matrix/affine-inverse-gap-stopping-certificate [])
         'rows 'offset 'approximate 'fixed-point
         (from-nnrat rate-value)
         (from-nnrat gap-value)
         (from-nnrat inverse-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              rate-value)
         (app (function/const* 'signed/zero-at-most-from-nnrat [])
              inverse-value)
         (app (function/const* 'signed/general-rate-plus-gap-one [])
              'ap 'gp)
         (app (function/const* 'signed/general-inverse-times-gap-one [])
              'ap 'gp)
         'shape 'offset-shape 'positive-rows 'bounded-sums 'fixed
         'threshold 'residual-at-most-threshold)))}))

(def definition-specs [])
(def theorem-specs
  [general-rate-plus-gap-spec
   general-inverse-times-gap-spec
   from-nnrat-add-spec
   signed-general-rate-plus-gap-spec
   signed-general-inverse-times-gap-spec
   affine-general-rate-fixed-point-residual-bound-spec
   affine-general-rate-stopping-certificate-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-inverse-gap-certificate])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'signed/from-nnrat-respects-equivalence :signed-geometric-bridge bridge/from-nnrat-respects-equivalence-spec) (extend-spec-if-missing 'signed/from-nnrat-multiply :signed-geometric-bridge bridge/from-nnrat-multiply-spec) (support/extend-with :finite-matrix-affine-general-rate-certificate theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-general-rate-certificate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
