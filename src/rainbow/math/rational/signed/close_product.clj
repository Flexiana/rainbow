(ns rainbow.math.rational.signed.close-product
  "Brick 4 (band) of limit-product: the product close-band.

  analysis/close-product : given close L es x, close M et y, and a magnitude bound
  |x| <= B, conclude close (L*M) (B*et + |M|*es) (x*y).

  Proof: read d(x,L)<=es and d(y,M)<=et off the bands; the bilinear
  analysis/distance-product gives d(x*y,L*M) <= |x|*d(y,M) + |M|*d(x,L); product
  monotonicity (|x|<=B, distances/absolutes nonnegative) bounds that by B*et + |M|*es;
  then convert d(x*y,L*M) <= bound back to a close-band. Axiom-free; additive."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-product :as distance-product]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.convergence :as convergence]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist* [a b] (app (function/const* 'signed/distance []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- close* [L e x] (app (function/const* 'analysis/close []) L e x))
(defn- eq-refl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- le-tr [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- lmono [c a b h0 hab] (app (function/const* 'signed/multiply-left-monotone []) c a b h0 hab))
(defn- rmono [c a b h0 hab] (app (function/const* 'signed/multiply-right-monotone []) c a b h0 hab))
(defn- dist-nn [a b] (app (function/const* 'signed/distance-nonnegative []) a b))
(defn- abs-nn [x] (app (function/const* 'signed/absolute-nonnegative []) x))
(defn- dist-of-close [l r e h1 h2] (app (function/const* 'signed/distance-at-most-of-additive-closeness []) l r e h1 h2))
(defn- ac-of-dist [l r e h] (app (function/const* 'signed/additive-closeness-of-distance-at-most []) l r e h))
(defn- au-of-sub [a b c h] (app (function/const* 'signed/additive-upper-of-subtract-at-most []) a b c h))
(defn- sub-of-au [a b c h] (app (function/const* 'signed/subtract-at-most-of-additive-upper []) a b c h))
(defn- distprod [x y L M] (app (function/const* 'analysis/distance-product []) x y L M))
(defn- p-left [P Q h] (app (function/const* 'proposition/left []) P Q h))
(defn- p-right [P Q h] (app (function/const* 'proposition/right []) P Q h))
(defn- conjoin [P Q p q] (app (function/const* 'proposition/conjoin []) P Q p q))

;; d(z,C) <= eps  from  close C eps z
(defn- dist-from-close [C eps z hclose]
  (let [P (sle (ssub C eps) z)                 ; C - eps <= z
        Q (sle z (sadd C eps))                 ; z <= C + eps
        lo (p-left P Q hclose)                 ; C - eps <= z
        hi (p-right P Q hclose)                ; z <= C + eps  (= left-close for d(z,C))
        ;; right-close: C <= z + eps ; from lo via additive-upper + commute
        Cle (au-of-sub C eps z lo)             ; C <= eps + z
        Cle2 (le-resp C C (sadd eps z) (sadd z eps)
                      (eq-refl C) (add-comm eps z) Cle)]  ; C <= z + eps
    (dist-of-close z C eps hi Cle2)))          ; d(z,C) <= eps

(def close-product-spec
  {:name 'analysis/close-product
   :universes []
   :type (function/forall
          [['x signed] ['y signed] ['L signed] ['M signed] ['es signed] ['et signed] ['B signed]
           ['hLx (close* 'L 'es 'x)] ['hMy (close* 'M 'et 'y)] ['hxB (sle (abs* 'x) 'B)]]
          (close* (smul 'L 'M) (sadd (smul 'B 'et) (smul (abs* 'M) 'es)) (smul 'x 'y)))
   :value
   (function/lam
    [['x signed] ['y signed] ['L signed] ['M signed] ['es signed] ['et signed] ['B signed]
     ['hLx (close* 'L 'es 'x)] ['hMy (close* 'M 'et 'y)] ['hxB (sle (abs* 'x) 'B)]]
    (let [xy (smul 'x 'y) LM (smul 'L 'M)
          dxL (dist-from-close 'L 'es 'x 'hLx)     ; d(x,L) <= es
          dyM (dist-from-close 'M 'et 'y 'hMy)     ; d(y,M) <= et
          Bnn (le-tr szero (abs* 'x) 'B (abs-nn 'x) 'hxB)   ; 0 <= B
          ;; |x|*d(y,M) <= B*d(y,M) <= B*et
          s1 (rmono (dist* 'y 'M) (abs* 'x) 'B (dist-nn 'y 'M) 'hxB)  ; |x|*d(y,M) <= B*d(y,M)
          s2 (lmono 'B (dist* 'y 'M) 'et Bnn dyM)                     ; B*d(y,M) <= B*et
          left-bnd (le-tr (smul (abs* 'x) (dist* 'y 'M)) (smul 'B (dist* 'y 'M)) (smul 'B 'et) s1 s2)
          ;; |M|*d(x,L) <= |M|*es
          right-bnd (lmono (abs* 'M) (dist* 'x 'L) 'es (abs-nn 'M) dxL)  ; |M|*d(x,L) <= |M|*es
          sum-bnd (add-mono (smul (abs* 'x) (dist* 'y 'M)) (smul 'B 'et)
                            (smul (abs* 'M) (dist* 'x 'L)) (smul (abs* 'M) 'es)
                            left-bnd right-bnd)   ; |x|*d(y,M)+|M|*d(x,L) <= B*et+|M|*es
          dp (distprod 'x 'y 'L 'M)               ; d(x*y,L*M) <= |x|*d(y,M)+|M|*d(x,L)
          bound (sadd (smul 'B 'et) (smul (abs* 'M) 'es))
          dbound (le-tr (dist* xy LM)
                        (sadd (smul (abs* 'x) (dist* 'y 'M)) (smul (abs* 'M) (dist* 'x 'L)))
                        bound dp sum-bnd)         ; d(x*y,L*M) <= bound
          ;; convert to close (L*M) bound (x*y)
          ac (ac-of-dist xy LM bound dbound)      ; (x*y <= L*M+bound) AND (L*M <= x*y+bound)
          Pac (sle xy (sadd LM bound))
          Qac (sle LM (sadd xy bound))
          hi (p-left Pac Qac ac)                  ; x*y <= L*M+bound   (= second conjunct of close)
          lo-pre (p-right Pac Qac ac)             ; L*M <= x*y+bound
          ;; commute x*y+bound -> bound+x*y so subtract-at-most moves BOUND to the left
          lo-pre2 (le-resp LM LM (sadd xy bound) (sadd bound xy)
                           (eq-refl LM) (add-comm xy bound) lo-pre)  ; L*M <= bound+x*y
          lo (sub-of-au LM bound xy lo-pre2)]     ; L*M - bound <= x*y  (= first conjunct)
      (conjoin (sle (ssub LM bound) xy) (sle xy (sadd LM bound)) lo hi)))})

(def theorem-specs [close-product-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distance-product rainbow.math.rational.signed.additive-distance rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.convergence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-close-product theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.close-product))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
