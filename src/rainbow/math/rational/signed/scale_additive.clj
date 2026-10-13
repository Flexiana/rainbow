(ns rainbow.math.rational.signed.scale-additive
  "Nonnegative-rational scaling distributes over signed addition up to
  Grothendieck equivalence.

    scale c (a + b)  ~  scale c a + scale c b

  After unfolding, both sides of signed equivalence are the same four scaled
  components under different addition trees.  The verified nnrat ring
  normalizer constructs the proof; the kernel checks it without axioms."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.temporal-difference :as temporal-difference]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value] (app (function/const* 'signed/positive []) value))
(defn- negative [value] (app (function/const* 'signed/negative []) value))
(defn- add [left right] (app (function/const* 'signed/add []) left right))
(defn- scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))

(def scale-additive-spec
  {:name 'signed/scale-additive :universes []
   :type
   (function/forall
    [['rate nnrat] ['left signed] ['right signed]]
    (equivalent
     (scale 'rate (add 'left 'right))
     (add (scale 'rate 'left) (scale 'rate 'right))))
   :value
   (function/lam
    [['rate nnrat] ['left signed] ['right signed]]
    (let [left-positive
          (ring/rmul 'rate
                     (ring/radd (positive 'left) (positive 'right)))
          left-negative
          (ring/rmul 'rate
                     (ring/radd (negative 'left) (negative 'right)))
          right-positive
          (ring/radd (ring/rmul 'rate (positive 'left))
                     (ring/rmul 'rate (positive 'right)))
          right-negative
          (ring/radd (ring/rmul 'rate (negative 'left))
                     (ring/rmul 'rate (negative 'right)))]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def definition-specs [])
(def theorem-specs [scale-additive-spec])

(defn- extend-scale-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment 'signed/scale)
    checked-environment
    (support/extend-with checked-environment :temporal-difference
                         [temporal-difference/scale-spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      extend-scale-if-missing
      ring/extend-environment
      (support/extend-with :signed-scale-additive theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
