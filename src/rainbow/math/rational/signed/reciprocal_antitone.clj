(ns rainbow.math.rational.signed.reciprocal-antitone
  "B4 of the limit-reciprocal arc: reciprocal reverses order on positives, plus the two
  reusable order<->subtract-nonneg bridges it needs.

    signed/nonnegative-subtract-of-at-most : x <= y -> nonnegative (y - x)
    signed/at-most-of-nonnegative-subtract : nonnegative (a - b) -> b <= a
    signed/reciprocal-antitone :
      nonnegative x -> 1<=num(mag(x*x)) -> 1<=num(mag(y*y)) -> x <= y ->
      reciprocal y <= reciprocal x

  The antitone proof REUSES the reciprocal-difference identity (b106532):
  recip x - recip y ~ (recip x * recip y) * (y - x), whose RHS is >= 0 (product of
  nonnegatives: reciprocal-nonnegative twice + the y-x bridge), so recip x - recip y >= 0,
  i.e. recip y <= recip x. Everything is done through `0 <= .` (signed at-most zero),
  since signed/nonnegative-respects-equivalence is absent. Axiom-free; additive; does not
  touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.reciprocal-difference :as recip-diff]
            [rainbow.math.rational.signed.reciprocal-nonnegative :as recip-nn]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.recovery-laws :as recovery-laws]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sneg [a] (app (function/const* 'signed/negate []) a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- reciprocal [x] (app (function/const* 'signed/reciprocal []) x))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- pos-hyp [x] (nat-le (succ zero) (numr (mag (smul x x)))))
;; wrappers
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- add-zero-r [c] (app (function/const* 'signed/add-zero-right []) c))
(defn- add-right-mono [a b c h] (app (function/const* 'signed/add-right-monotone []) a b c h))
(defn- sub-self-zero [c] (app (function/const* 'signed/subtract-self-equivalent-zero []) c))
(defn- sub-then-add [a b] (app (function/const* 'signed/subtract-then-add []) a b))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- nn-of-0le [x h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) x h))
(defn- zle-of-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- mult-nn [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- recip-nonneg [x h] (app (function/const* 'signed/reciprocal-nonnegative []) x h))
(defn- recip-difference [a b ha hb] (app (function/const* 'signed/reciprocal-difference []) a b ha hb))

;; --- bridge (i): x <= y -> nonneg (y - x) ---
(def nonnegative-subtract-of-at-most-spec
  {:name 'signed/nonnegative-subtract-of-at-most
   :universes []
   :type (function/forall [['x signed] ['y signed] ['hxy (sle 'x 'y)]]
                          (nonneg (ssub 'y 'x)))
   :value
   (function/lam [['x signed] ['y signed] ['hxy (sle 'x 'y)]]
                 (let [m (add-right-mono 'x 'y (sneg 'x) 'hxy)          ; x+(-x) <= y+(-x)
                       zle (le-resp (sadd 'x (sneg 'x)) szero (sadd 'y (sneg 'x)) (ssub 'y 'x)
                                    (sub-self-zero 'x) (erefl (ssub 'y 'x)) m)]  ; 0 <= y - x
                   (nn-of-0le (ssub 'y 'x) zle)))})

;; --- bridge (ii): nonneg (a - b) -> b <= a ---
(def at-most-of-nonnegative-subtract-spec
  {:name 'signed/at-most-of-nonnegative-subtract
   :universes []
   :type (function/forall [['a signed] ['b signed] ['h (nonneg (ssub 'a 'b))]]
                          (sle 'b 'a))
   :value
   (function/lam [['a signed] ['b signed] ['h (nonneg (ssub 'a 'b))]]
                 (let [zab (zle-of-nn (ssub 'a 'b) 'h)                   ; 0 <= a - b
                       m (add-right-mono szero (ssub 'a 'b) 'b zab)      ; 0+b <= (a-b)+b
                       zb (eqv-tr (sadd szero 'b) (sadd 'b szero) 'b
                                  (add-comm szero 'b) (add-zero-r 'b))]  ; 0+b ~ b
                   (le-resp (sadd szero 'b) 'b (sadd (ssub 'a 'b) 'b) 'a
                            zb (sub-then-add 'a 'b) m)))})               ; b <= a

;; --- B4: reciprocal-antitone ---
(def reciprocal-antitone-spec
  {:name 'signed/reciprocal-antitone
   :universes []
   :type (function/forall
          [['x signed] ['y signed]
           ['hx (nonneg 'x)] ['hx0 (pos-hyp 'x)] ['hy0 (pos-hyp 'y)] ['hxy (sle 'x 'y)]]
          (sle (reciprocal 'y) (reciprocal 'x)))
   :value
   (function/lam
    [['x signed] ['y signed]
     ['hx (nonneg 'x)] ['hx0 (pos-hyp 'x)] ['hy0 (pos-hyp 'y)] ['hxy (sle 'x 'y)]]
    (let [rx (reciprocal 'x) ry (reciprocal 'y)
          hy (nn-of-0le 'y (le-trans szero 'x 'y (zle-of-nn 'x 'hx) 'hxy))   ; nonneg y
          nn-rxry (mult-nn rx ry (recip-nonneg 'x 'hx) (recip-nonneg 'y hy)) ; nonneg (rx*ry)
          nn-yx (app (function/const* 'signed/nonnegative-subtract-of-at-most []) 'x 'y 'hxy) ; nonneg (y-x)
          P (smul (smul rx ry) (ssub 'y 'x))
          nn-P (mult-nn (smul rx ry) (ssub 'y 'x) nn-rxry nn-yx)            ; nonneg P
          diff (recip-difference 'x 'y 'hx0 'hy0)                           ; (rx - ry) ~ P
          zP (zle-of-nn P nn-P)                                             ; 0 <= P
          zD (le-resp szero szero P (ssub rx ry)
                      (erefl szero) (eqv-sym (ssub rx ry) P diff) zP)       ; 0 <= rx - ry
          nn-D (nn-of-0le (ssub rx ry) zD)]                                 ; nonneg (rx - ry)
      (app (function/const* 'signed/at-most-of-nonnegative-subtract []) rx ry nn-D)))}) ; ry <= rx

(def theorem-specs
  [nonnegative-subtract-of-at-most-spec
   at-most-of-nonnegative-subtract-spec
   reciprocal-antitone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      recip-diff/extend-environment
      recip-nn/extend-environment
      multiply-order/extend-environment
      order-monotone/extend-environment
      order-transitivity/extend-environment
      order-respects/extend-environment
      unit-laws/extend-environment
      recovery-laws/extend-environment
      (support/extend-with :signed-reciprocal-antitone theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
