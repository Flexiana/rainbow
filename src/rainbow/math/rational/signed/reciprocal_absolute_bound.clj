(ns rainbow.math.rational.signed.reciprocal-absolute-bound
  "Layer A of the limit-reciprocal assembly: bound the absolute reciprocal of x by the
  reciprocal of a positive lower bound on |x|.

    signed/absolute-reciprocal-at-most-of-lower-bound :
      nonneg b -> 1<=num(mag(b*b)) -> 1<=num(mag(x*x)) -> 1<=num(mag(|x|*|x|)) -> b <= |x| ->
      |reciprocal x| <= reciprocal b

  |reciprocal x| ~ reciprocal|x| by uniqueness of inverse (both times |x| give 1:
  absolute-reciprocal-times-self and multiply-reciprocal-self), then reciprocal-antitone on
  b <= |x| gives reciprocal|x| <= reciprocal b. In the assembly, b = |L|/2 and the
  convergent-bounded-below lower bound |L|/2 <= |s n| yield the CONSTANT bound
  |reciprocal (s n)| <= reciprocal(|L|/2) = 2/|L|. Axiom-free; additive; no LP-checker touch."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute-reciprocal-times-self :as arts]
            [rainbow.math.rational.signed.reciprocal :as reciprocal]
            [rainbow.math.rational.signed.inverse-unique :as inverse-unique]
            [rainbow.math.rational.signed.reciprocal-antitone :as antitone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- recip [x] (app (function/const* 'signed/reciprocal []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- pos-hyp [v] (nat-le (succ zero) (numr (mag (smul v v)))))
(defn- one [] (function/const* 'signed/one []))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- arts-self [x h] (app (function/const* 'signed/absolute-reciprocal-times-self []) x h))
(defn- self-inv [x h] (app (function/const* 'signed/multiply-reciprocal-self []) x h))
(defn- inv-unique [u v w hu hv] (app (function/const* 'signed/inverse-unique []) u v w hu hv))
(defn- recip-antitone [x y hx hx0 hy0 hxy] (app (function/const* 'signed/reciprocal-antitone []) x y hx hx0 hy0 hxy))

(def absolute-reciprocal-at-most-of-lower-bound-spec
  {:name 'signed/absolute-reciprocal-at-most-of-lower-bound
   :universes []
   :type (function/forall
          [['b signed] ['x signed]
           ['hbnn (nonneg 'b)] ['hb2 (pos-hyp 'b)] ['hx2 (pos-hyp 'x)]
           ['habsx2 (pos-hyp (abs* 'x))] ['hbx (sle 'b (abs* 'x))]]
          (sle (abs* (recip 'x)) (recip 'b)))
   :value
   (function/lam
    [['b signed] ['x signed]
     ['hbnn (nonneg 'b)] ['hb2 (pos-hyp 'b)] ['hx2 (pos-hyp 'x)]
     ['habsx2 (pos-hyp (abs* 'x))] ['hbx (sle 'b (abs* 'x))]]
    (let [rx (recip 'x)
          ax (abs* 'x)
          rax (recip ax)
          ;; |rx| * |x| ~ 1
          u-w (arts-self 'x 'hx2)
          ;; reciprocal|x| * |x| ~ 1  (commute of |x|*reciprocal|x| ~ 1)
          v-w (eqv-tr (smul rax ax) (smul ax rax) (one)
                      (mult-comm rax ax) (self-inv ax 'habsx2))
          ;; |rx| ~ reciprocal|x|  (uniqueness of inverse of |x|)
          rx-rax (inv-unique (abs* rx) rax ax u-w v-w)
          ;; reciprocal|x| <= reciprocal b  (antitone on b <= |x|)
          anti (recip-antitone 'b ax 'hbnn 'hb2 'habsx2 'hbx)]
      ;; |rx| <= reciprocal b
      (le-resp rax (abs* rx) (recip 'b) (recip 'b)
               (eqv-sym (abs* rx) rax rx-rax) (erefl (recip 'b)) anti)))})

(def theorem-specs [absolute-reciprocal-at-most-of-lower-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.absolute-reciprocal-times-self rainbow.math.rational.signed.reciprocal rainbow.math.rational.signed.inverse-unique rainbow.math.rational.signed.reciprocal-antitone rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.order-respects])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-reciprocal-absolute-bound theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.reciprocal-absolute-bound))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
