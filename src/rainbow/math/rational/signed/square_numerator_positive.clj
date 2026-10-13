(ns rainbow.math.rational.signed.square-numerator-positive
  "B6d of the limit-reciprocal arc: the positivity derivation the assembly calls.

    signed/square-numerator-positive-of-lower-bound :
      0 <= a -> 1 <= num(mag(a*a)) -> a <= b -> 1 <= num(mag(b*b))

  Composes B6a/B6b/B6c: 0<=a & a<=b give a*a <= b*b (square-monotone); both squares are
  nonnegative (square-nonnegative), so mag(a*a) <= mag(b*b) (magnitude-monotone); and
  positivity transfers upward (positive-of-at-most). The hypothesis/goal `1 <= num(mag(.))`
  is definitionally nnrat/positive (mag .), so B6c applies directly. Called in the assembly
  with a = |L|/2 and b = |s n| to get 1 <= num(mag(s n * s n)), enabling reciprocal-difference/
  antitone/absolute-reciprocal on s n. Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.square-monotone :as square-monotone]
            [rainbow.math.rational.signed.magnitude-monotone :as magnitude-monotone]
            [rainbow.math.rational.nnrat.positive-monotone :as positive-monotone]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- pos-num [x] (nat-le (succ zero) (numr (mag (smul x x)))))
(defn- sq-mono [a b ha hab] (app (function/const* 'signed/square-monotone []) a b ha hab))
(defn- square-nn [x] (app (function/const* 'signed/square-nonnegative []) x))
(defn- mag-mono [a b ha hb hab] (app (function/const* 'signed/magnitude-monotone []) a b ha hb hab))
(defn- pos-of-at-most [p q hp hpq] (app (function/const* 'nnrat/positive-of-at-most []) p q hp hpq))

(def square-numerator-positive-of-lower-bound-spec
  {:name 'signed/square-numerator-positive-of-lower-bound
   :universes []
   :type (function/forall
          [['a signed] ['b signed] ['ha (sle szero 'a)] ['hpos (pos-num 'a)] ['hab (sle 'a 'b)]]
          (pos-num 'b))
   :value
   (function/lam
    [['a signed] ['b signed] ['ha (sle szero 'a)] ['hpos (pos-num 'a)] ['hab (sle 'a 'b)]]
    (let [sq-le (sq-mono 'a 'b 'ha 'hab)                                   ; a*a <= b*b
          mag-le (mag-mono (smul 'a 'a) (smul 'b 'b) (square-nn 'a) (square-nn 'b) sq-le)]  ; mag(a*a) <= mag(b*b)
      ;; hpos : 1<=num(mag(a*a)) == nnrat/positive (mag(a*a)); result == 1<=num(mag(b*b))
      (pos-of-at-most (mag (smul 'a 'a)) (mag (smul 'b 'b)) 'hpos mag-le)))})

(def theorem-specs [square-numerator-positive-of-lower-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.square-monotone rainbow.math.rational.signed.magnitude-monotone rainbow.math.rational.nnrat.positive-monotone rainbow.math.linear.vector.norm-nonnegative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-numerator-positive theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-numerator-positive))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
