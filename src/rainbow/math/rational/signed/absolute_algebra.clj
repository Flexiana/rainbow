(ns rainbow.math.rational.signed.absolute-algebra
  "Quotient-safe algebra for native signed absolute value.

  Signed rationals are Grothendieck pairs, so observable algebra is stated with
  `signed/equivalent`.  This layer proves that lattice maximum and absolute
  value respect that equivalence, that absolute value ignores sign, normalizes
  zero, and is idempotent.  These are the scalar well-definedness laws needed
  before defining signed distance and finite-vector sup metrics.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute :as absolute]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- magnitude [value]
  (app (function/const* 'signed/absolute []) value))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))
(defn- max-left [left right]
  (app (function/const* 'signed/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- max-below [left right upper left-upper right-upper]
  (app (function/const* 'signed/at-most-max [])
       left right upper left-upper right-upper))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- equivalent-to-at-most [left right same]
  (order-respects
   left left left right
   (equivalent-reflexive left) same (order-reflexive left)))

(def max-respects-equivalence-spec
  {:name 'signed/max-respects-equivalence :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['same-left (veq 'left 'left-prime)]
     ['same-right (veq 'right 'right-prime)]]
    (veq (maximum 'left 'right)
         (maximum 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['same-left (veq 'left 'left-prime)]
     ['same-right (veq 'right 'right-prime)]]
    (let [source (maximum 'left 'right)
          target (maximum 'left-prime 'right-prime)
          left-forward
          (transitive
           'left 'left-prime target
           (equivalent-to-at-most 'left 'left-prime 'same-left)
           (max-left 'left-prime 'right-prime))
          right-forward
          (transitive
           'right 'right-prime target
           (equivalent-to-at-most 'right 'right-prime 'same-right)
           (max-right 'left-prime 'right-prime))
          forward
          (max-below 'left 'right target left-forward right-forward)
          left-backward
          (transitive
           'left-prime 'left source
           (equivalent-to-at-most
            'left-prime 'left
            (equivalent-symmetric 'left 'left-prime 'same-left))
           (max-left 'left 'right))
          right-backward
          (transitive
           'right-prime 'right source
           (equivalent-to-at-most
            'right-prime 'right
            (equivalent-symmetric 'right 'right-prime 'same-right))
           (max-right 'left 'right))
          backward
          (max-below 'left-prime 'right-prime source
                     left-backward right-backward)]
      (antisymmetric source target forward backward)))})

(def absolute-respects-equivalence-spec
  {:name 'signed/absolute-respects-equivalence :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (veq 'left 'right)]]
    (veq (magnitude 'left) (magnitude 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (veq 'left 'right)]]
    (app
     (function/const* 'signed/max-respects-equivalence [])
     'left (negate 'left) 'right (negate 'right)
     'same
     (app (function/const* 'signed/negate-respects-equivalence [])
          'left 'right 'same)))})

(def absolute-negate-spec
  {:name 'signed/absolute-negate :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (magnitude (negate 'value)) (magnitude 'value)))
   :value
   (function/lam
    [['value signed]]
    (let [negated (negate 'value)
          twice-negated (negate negated)
          left-magnitude (magnitude negated)
          right-magnitude (magnitude 'value)
          twice-same
          (app (function/const* 'signed/negate-involutive []) 'value)
          twice-below-right
          (order-respects
           twice-negated 'value right-magnitude right-magnitude
           twice-same (equivalent-reflexive right-magnitude)
           (max-left 'value negated))
          forward
          (max-below
           negated twice-negated right-magnitude
           (max-right 'value negated)
           twice-below-right)
          value-same-twice
          (equivalent-symmetric twice-negated 'value twice-same)
          value-below-left
          (order-respects
           'value twice-negated left-magnitude left-magnitude
           value-same-twice (equivalent-reflexive left-magnitude)
           (max-right negated twice-negated))
          backward
          (max-below
           'value negated left-magnitude
           value-below-left
           (max-left negated twice-negated))]
      (antisymmetric left-magnitude right-magnitude forward backward)))})

(def absolute-zero-spec
  {:name 'signed/absolute-zero :universes []
   :type (veq (magnitude signed-zero) signed-zero)
   :value
   (let [zero-max (magnitude signed-zero)]
     (antisymmetric
      zero-max signed-zero
      (max-below signed-zero signed-zero signed-zero
                 (order-reflexive signed-zero)
                 (order-reflexive signed-zero))
      (max-left signed-zero signed-zero)))})

(def absolute-idempotent-spec
  {:name 'signed/absolute-idempotent :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (magnitude (magnitude 'value)) (magnitude 'value)))
   :value
   (function/lam
    [['value signed]]
    (let [absolute-value (magnitude 'value)
          negated-absolute (negate absolute-value)
          nonnegative
          (app (function/const* 'signed/absolute-nonnegative []) 'value)
          negated-below-zero
          (app (function/const* 'signed/negate-reverses-order [])
               signed-zero absolute-value nonnegative)
          negated-below-absolute
          (transitive negated-absolute signed-zero absolute-value
                      negated-below-zero nonnegative)
          upper
          (max-below absolute-value negated-absolute absolute-value
                     (order-reflexive absolute-value)
                     negated-below-absolute)
          lower (max-left absolute-value negated-absolute)]
      (antisymmetric (magnitude absolute-value) absolute-value
                     upper lower)))})

(def definition-specs [])
(def theorem-specs
  [max-respects-equivalence-spec
   absolute-respects-equivalence-spec
   absolute-negate-spec
   absolute-zero-spec
   absolute-idempotent-spec])

(defn extend-environment [env]
  (-> env
      absolute/extend-environment
      uniqueness/extend-environment
      equivalence/extend-environment
      (support/extend-with :signed-absolute-algebra theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
