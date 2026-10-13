(ns rainbow.math.rational.signed.square-numerator-positive-of-absolute
  "B6f prerequisite (s-n positivity transfer): a lower bound on |x| makes x*x have
  positive magnitude-numerator.

    signed/square-numerator-positive-of-absolute-bound :
      0 <= b -> 1 <= num(mag(b*b)) -> b <= |x| -> 1 <= num(mag(x*x))

  B6d (square-numerator-positive-of-lower-bound) on b <= |x| gives 1 <= num(mag(|x|*|x|));
  then transfer |x|*|x| ~ x*x (absolute-multiply + x*x nonnegative) via magnitude-monotone +
  positive-of-at-most. In the limit-reciprocal assembly this is called with b = |L|/2 and the
  bound |L|/2 <= |s n| to obtain 1 <= num(mag(s n * s n)) -- the nonzero fact
  reciprocal-difference / absolute-reciprocal-times-self / reciprocal-antitone need for s n.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.square-numerator-positive :as sq-num-pos]
            [rainbow.math.rational.signed.absolute-multiply :as absolute-multiply]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.magnitude-monotone :as magnitude-monotone]
            [rainbow.math.rational.nnrat.positive-monotone :as positive-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- pos-num [x] (nat-le (succ zero) (numr (mag (smul x x)))))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- sq-num-pos-lb [a b ha hpos hab]
  (app (function/const* 'signed/square-numerator-positive-of-lower-bound []) a b ha hpos hab))
(defn- abs-mul [a b] (app (function/const* 'signed/absolute-multiply []) a b))
(defn- abs-of-nn [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- square-nn [v] (app (function/const* 'signed/square-nonnegative []) v))
(defn- zle-of-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- mag-mono [a b ha hb hab] (app (function/const* 'signed/magnitude-monotone []) a b ha hb hab))
(defn- pos-at-most [p q hp hpq] (app (function/const* 'nnrat/positive-of-at-most []) p q hp hpq))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))

(def square-numerator-positive-of-absolute-bound-spec
  {:name 'signed/square-numerator-positive-of-absolute-bound
   :universes []
   :type (function/forall
          [['b signed] ['x signed] ['hb0 (sle szero 'b)] ['hbpos (pos-num 'b)] ['hbx (sle 'b (abs* 'x))]]
          (pos-num 'x))
   :value
   (function/lam
    [['b signed] ['x signed] ['hb0 (sle szero 'b)] ['hbpos (pos-num 'b)] ['hbx (sle 'b (abs* 'x))]]
    (let [sqx (smul 'x 'x)
          sqax (smul (abs* 'x) (abs* 'x))
          absx2-pos (sq-num-pos-lb 'b (abs* 'x) 'hb0 'hbpos 'hbx)     ; 1<=num(mag(|x|^2)) = nnpos(mag sqax)
          ;; sqax ~ sqx :  x*x ~ |x*x| ~ |x|*|x|
          sqx-sqax (eqv-tr sqx (abs* sqx) sqax
                           (eqv-sym (abs* sqx) sqx (abs-of-nn sqx (zle-of-nn sqx (square-nn 'x))))
                           (abs-mul 'x 'x))                            ; sqx ~ sqax
          sqax-sqx (eqv-sym sqx sqax sqx-sqax)                        ; sqax ~ sqx
          sqax<=sqx (le-resp sqax sqax sqax sqx (erefl sqax) sqax-sqx (le-refl sqax))  ; sqax <= sqx
          mag-le (mag-mono sqax sqx (square-nn (abs* 'x)) (square-nn 'x) sqax<=sqx)]   ; mag sqax <= mag sqx
      (pos-at-most (mag sqax) (mag sqx) absx2-pos mag-le)))})          ; nnpos(mag sqx) = pos-num x

(def theorem-specs [square-numerator-positive-of-absolute-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.square-numerator-positive rainbow.math.rational.signed.absolute-multiply rainbow.math.rational.signed.absolute-sign rainbow.math.linear.vector.norm-nonnegative rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.magnitude-monotone rainbow.math.rational.nnrat.positive-monotone rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.order-respects])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-numerator-positive-of-absolute theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-numerator-positive-of-absolute))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
