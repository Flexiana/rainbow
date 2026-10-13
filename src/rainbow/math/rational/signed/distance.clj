(ns rainbow.math.rational.signed.distance
  "A quotient-safe scalar metric interface for signed rationals.

  `signed/distance a b` is `|a-b|`.  Its laws establish nonnegativity,
  congruence, symmetry, self-zero, exact separation up to signed equivalence,
  and the two-row linear encoding of a radius bound.  The module reuses only
  the scalar specs from older vector/counterfactual developments, keeping the
  metric foundation independent of those larger representations.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.counterfactual-distance-separation :as separation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.absolute-algebra :as absolute-algebra]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-add]
            [rainbow.math.rational.signed.negate-additive :as negate-additive]
            [rainbow.math.rational.signed.unit-laws :as unit]
            [rainbow.math.linear.vector.dot-subtract :as subtract-laws]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- absolute [value]
  (app (function/const* 'signed/absolute []) value))
(defn- distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))

(def distance-spec
  {:name 'signed/distance :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (absolute (subtract 'left 'right)))})

(def negate-subtract-spec
  {:name 'signed/negate-subtract :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (veq (negate (subtract 'left 'right))
         (subtract 'right 'left)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [start (negate (subtract 'left 'right))
          distributed (add (negate 'left)
                           (negate (negate 'right)))
          reduced (add (negate 'left) 'right)
          finish (subtract 'right 'left)
          distribute
          (app (function/const* 'signed/negate-additive [])
               'left (negate 'right))
          eliminate-double-negation
          (app
           (function/const* 'signed/add-respects-equivalence [])
           (negate 'left) (negate 'left)
           (negate (negate 'right)) 'right
           (equivalent-reflexive (negate 'left))
           (app (function/const* 'signed/negate-involutive []) 'right))
          commute
          (app (function/const* 'signed/add-commutative [])
               (negate 'left) 'right)]
      (equivalent-transitive
       start reduced finish
       (equivalent-transitive
        start distributed reduced
        distribute eliminate-double-negation)
       commute)))})

(def distance-unfold-spec
  {:name 'signed/distance-unfold :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (veq (distance 'left 'right)
         (absolute (subtract 'left 'right))))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (equivalent-reflexive (distance 'left 'right)))})

(def distance-nonnegative-spec
  {:name 'signed/distance-nonnegative :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (sle signed-zero (distance 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (app (function/const* 'signed/absolute-nonnegative [])
         (subtract 'left 'right)))})

(def distance-respects-equivalence-spec
  {:name 'signed/distance-respects-equivalence :universes []
   :type
   (function/forall
    [['left signed] ['left-prime signed]
     ['right signed] ['right-prime signed]
     ['same-left (veq 'left 'left-prime)]
     ['same-right (veq 'right 'right-prime)]]
    (veq (distance 'left 'right)
         (distance 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left signed] ['left-prime signed]
     ['right signed] ['right-prime signed]
     ['same-left (veq 'left 'left-prime)]
     ['same-right (veq 'right 'right-prime)]]
    (app
     (function/const* 'signed/absolute-respects-equivalence [])
     (subtract 'left 'right)
     (subtract 'left-prime 'right-prime)
     (app (function/const* 'signed/subtract-respects-equivalence [])
          'left 'left-prime 'right 'right-prime
          'same-left 'same-right)))})

(def distance-symmetric-spec
  {:name 'signed/distance-symmetric :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (veq (distance 'left 'right)
         (distance 'right 'left)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [forward (subtract 'left 'right)
          reverse (subtract 'right 'left)
          negated-forward (negate forward)
          forward-absolute (absolute forward)
          negated-absolute (absolute negated-forward)
          reverse-absolute (absolute reverse)]
      (equivalent-transitive
       forward-absolute negated-absolute reverse-absolute
       (equivalent-symmetric
        negated-absolute forward-absolute
        (app (function/const* 'signed/absolute-negate []) forward))
       (app
        (function/const* 'signed/absolute-respects-equivalence [])
        negated-forward reverse
        (app (function/const* 'signed/negate-subtract [])
             'left 'right)))))})

(def distance-self-zero-spec
  {:name 'signed/distance-self-zero :universes []
   :type
   (function/forall
    [['value signed]]
    (veq (distance 'value 'value) signed-zero))
   :value
   (function/lam
    [['value signed]]
    (let [difference (subtract 'value 'value)
          difference-absolute (absolute difference)
          zero-absolute (absolute signed-zero)]
      (equivalent-transitive
       difference-absolute zero-absolute signed-zero
       (app
        (function/const* 'signed/absolute-respects-equivalence [])
        difference signed-zero
        (app (function/const* 'signed/subtract-self-equivalent-zero [])
             'value))
       (function/const* 'signed/absolute-zero []))))})

(def distance-zero-of-equivalent-spec
  {:name 'signed/distance-zero-of-equivalent :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (veq 'left 'right)]]
    (veq (distance 'left 'right) signed-zero))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (veq 'left 'right)]]
    (equivalent-transitive
     (distance 'left 'right) (distance 'left 'left) signed-zero
     (app
      (function/const* 'signed/distance-respects-equivalence [])
      'left 'left 'right 'left
      (equivalent-reflexive 'left)
      (equivalent-symmetric 'left 'right 'same))
     (app (function/const* 'signed/distance-self-zero []) 'left)))})

(def equivalent-of-distance-zero-spec
  {:name 'signed/equivalent-of-distance-zero :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['distance-zero (veq (distance 'left 'right) signed-zero)]]
    (veq 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['distance-zero (veq (distance 'left 'right) signed-zero)]]
    (let [difference (subtract 'left 'right)
          negated-difference (negate difference)
          magnitude (absolute difference)
          magnitude-below-zero
          (app (function/const* 'signed/equivalent-to-at-most [])
               magnitude signed-zero 'distance-zero)
          difference-below-zero
          (order-transitive
           difference magnitude signed-zero
           (app (function/const* 'signed/at-most-absolute []) difference)
           magnitude-below-zero)
          negated-below-zero
          (order-transitive
           negated-difference magnitude signed-zero
           (app (function/const* 'signed/negate-at-most-absolute [])
                difference)
           magnitude-below-zero)
          zero-below-double-negation
          (app (function/const* 'signed/negate-reverses-order [])
               negated-difference signed-zero negated-below-zero)
          twice-negated (negate negated-difference)
          zero-below-difference
          (order-respects
           signed-zero signed-zero twice-negated difference
           (equivalent-reflexive signed-zero)
           (app (function/const* 'signed/negate-involutive []) difference)
           zero-below-double-negation)
          difference-zero
          (antisymmetric difference signed-zero
                         difference-below-zero zero-below-difference)]
      (app
       (function/const* 'signed/subtract-zero-reflects-equivalence [])
       'left 'right difference-zero)))})

(def distance-zero-iff-equivalent-spec
  {:name 'signed/distance-zero-iff-equivalent :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (proposition/equivalence
     (veq (distance 'left 'right) signed-zero)
     (veq 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [distance-zero (veq (distance 'left 'right) signed-zero)
          same (veq 'left 'right)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       distance-zero same
       (function/lam
        [['zero-distance distance-zero]]
        (app (function/const* 'signed/equivalent-of-distance-zero [])
             'left 'right 'zero-distance))
       (function/lam
        [['equivalent same]]
        (app (function/const* 'signed/distance-zero-of-equivalent [])
             'left 'right 'equivalent)))))})

(def distance-bounded-iff-deviation-rows-spec
  {:name 'signed/distance-bounded-iff-deviation-rows :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['threshold signed]]
    (proposition/equivalence
     (sle (distance 'left 'right) 'threshold)
     (both (sle (subtract 'left 'right) 'threshold)
           (sle (negate (subtract 'left 'right)) 'threshold))))
   :value
   (function/lam
    [['left signed] ['right signed] ['threshold signed]]
    (app
     (function/const* 'signed/absolute-bounded-iff-deviation-rows [])
     (subtract 'left 'right) 'threshold))})

(def definition-specs [distance-spec])
(def theorem-specs
  [negate-subtract-spec
   distance-unfold-spec
   distance-nonnegative-spec
   distance-respects-equivalence-spec
   distance-symmetric-spec
   distance-self-zero-spec
   distance-zero-of-equivalent-spec
   equivalent-of-distance-zero-spec
   distance-zero-iff-equivalent-spec
   distance-bounded-iff-deviation-rows-spec])

(defn- extend-spec-if-missing
  [env alias producer spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env producer [spec])))

(defn extend-environment [env]
  (-> env
      absolute-algebra/extend-environment
      (extend-spec-if-missing
       'signed/negate-additive :signed-negate-additive
       negate-additive/negate-additive-spec)
      (extend-spec-if-missing
       'signed/equivalent-to-at-most :signed-unit-laws
       unit/equivalent-to-at-most-spec)
      (extend-spec-if-missing
       'signed/add-commutative :nnrat-commutative
       commutative/signed-add-commutative-spec)
      (extend-spec-if-missing
       'signed/add-respects-equivalence :signed-map-sum-algebra
       signed-add/add-respects-equivalence-spec)
      (extend-spec-if-missing
       'signed/equivalent-transitive :signed-map-sum-algebra
       signed-add/equivalent-transitive-spec)
      (extend-spec-if-missing
       'signed/subtract-self-equivalent-zero :signed-unit-laws
       unit/subtract-self-equivalent-zero-spec)
      (extend-spec-if-missing
       'signed/subtract-respects-equivalence :vector-dot-subtract
       subtract-laws/subtract-respects-equivalence-spec)
      (extend-spec-if-missing
       'signed/subtract-zero-reflects-equivalence
       :counterfactual-distance-separation
       separation/subtract-zero-reflects-equivalence-spec)
      (support/extend-with :signed-distance
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
