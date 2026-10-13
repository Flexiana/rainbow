(ns rainbow.math.rational.signed.magnitude-monotone
  "B6 prerequisite: magnitude is monotone on nonnegatives.

    signed/magnitude-monotone :
      nonnegative a -> nonnegative b -> a <= b -> nnrat/at-most (magnitude a) (magnitude b)

  Immediate: a ~ from-nnrat(magnitude a), b ~ from-nnrat(magnitude b) [from-nnrat-magnitude],
  so a <= b transports to from-nnrat(mag a) <= from-nnrat(mag b) [at-most-respects-equivalence],
  and from-nnrat-at-most-reverse drops it to the nnrat order. Reusable; feeds the limit-reciprocal
  assembly's positivity derivation (|s n| >= |L|/2 -> mag(s n^2) positive). Axiom-free; additive;
  does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.magnitude :as magnitude]
            [rainbow.math.rational.signed.geometric-bridge :as geometric-bridge]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- rle [a b] (app (function/const* 'nnrat/at-most []) a b))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- fnn-magn [x h] (app (function/const* 'signed/from-nnrat-magnitude []) x h))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- fnn-le-rev [a b h] (app (function/const* 'signed/from-nnrat-at-most-reverse []) a b h))

(def magnitude-monotone-spec
  {:name 'signed/magnitude-monotone
   :universes []
   :type (function/forall
          [['a signed] ['b signed] ['ha (nonneg 'a)] ['hb (nonneg 'b)] ['hab (sle 'a 'b)]]
          (rle (mag 'a) (mag 'b)))
   :value
   (function/lam
    [['a signed] ['b signed] ['ha (nonneg 'a)] ['hb (nonneg 'b)] ['hab (sle 'a 'b)]]
    (let [ea (fnn-magn 'a 'ha)                    ; a ~ from-nnrat (mag a)
          eb (fnn-magn 'b 'hb)                    ; b ~ from-nnrat (mag b)
          ord (le-resp 'a (fnn (mag 'a)) 'b (fnn (mag 'b)) ea eb 'hab)]  ; fnn(mag a) <= fnn(mag b)
      (fnn-le-rev (mag 'a) (mag 'b) ord)))})       ; mag a <= mag b (nnrat)

(def theorem-specs [magnitude-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      magnitude/extend-environment
      geometric-bridge/extend-environment
      order-respects/extend-environment
      (support/extend-with :signed-magnitude-monotone theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
