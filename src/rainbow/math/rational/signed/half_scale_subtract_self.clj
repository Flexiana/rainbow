(ns rainbow.math.rational.signed.half-scale-subtract-self
  "B6e of the limit-reciprocal arc: subtracting half of a value from itself leaves half.

    signed/half-scale-subtract-self : value - (1/2 * value) ~ 1/2 * value

  where 1/2 * value = smul (from-nnrat nnrat/half) value. Reuses the existing
  signed/half-scale-add-self (1/2 v + 1/2 v ~ v): rewrite value as (h + h), then
  (h + h) - h ~ h by associativity + subtract-self + add-zero-right. The assembly
  instantiates value = |L|, so convergent-bounded-below at radius (1/2)|L| yields
  (1/2)|L| <= |s n| (a fixed positive lower bound). Axiom-free; additive; does not touch
  the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness :as half-row]
            [rainbow.math.rational.signed.add-associative :as add-associative]
            [rainbow.math.linear.vector.dot-subtract :as dot-subtract]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.kkt-sufficiency :as kkt]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private signed-half
  (function/app (function/const* 'signed/from-nnrat []) (function/const* 'nnrat/half [])))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sneg [a] (app (function/const* 'signed/negate []) a))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- half-add-self [v] (app (function/const* 'signed/half-scale-add-self []) v))
(defn- add-assoc [a b c] (app (function/const* 'signed/add-associative []) a b c))
(defn- sub-resp [a ah b bh ha hb] (app (function/const* 'signed/subtract-respects-equivalence []) a ah b bh ha hb))
(defn- add-left-resp [a b c h] (app (function/const* 'signed/add-left-respects-equivalence []) a b c h))
(defn- sub-self-zero [c] (app (function/const* 'signed/subtract-self-equivalent-zero []) c))
(defn- add-zero-r [c] (app (function/const* 'signed/add-zero-right []) c))

(def half-scale-subtract-self-spec
  {:name 'signed/half-scale-subtract-self
   :universes []
   :type (function/forall [['value signed]]
                          (seqv (ssub 'value (smul signed-half 'value)) (smul signed-half 'value)))
   :value
   (function/lam
    [['value signed]]
    (let [h (smul signed-half 'value)
          hhv (half-add-self 'value)                              ; h + h ~ value
          ;; (value - h) ~ ((h+h) - h)
          s1 (sub-resp 'value (sadd h h) h h (eqv-sym (sadd h h) 'value hhv) (erefl h))
          ;; (h+h) - h ~ h+(h-h) ~ h+0 ~ h
          s2 (eqv-tr (ssub (sadd h h) h) (sadd h (ssub h h)) h
                     (add-assoc h h (sneg h))
                     (eqv-tr (sadd h (ssub h h)) (sadd h szero) h
                             (add-left-resp (ssub h h) szero h (sub-self-zero h))
                             (add-zero-r h)))]
      (eqv-tr (ssub 'value h) (ssub (sadd h h) h) h s1 s2)))})

(def theorem-specs [half-scale-subtract-self-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      half-row/extend-environment
      add-associative/extend-environment
      dot-subtract/extend-environment
      unit-laws/extend-environment
      kkt/extend-environment
      (support/extend-with :signed-half-scale-subtract-self theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
