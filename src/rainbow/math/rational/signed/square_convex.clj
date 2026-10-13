(ns rainbow.math.rational.signed.square-convex
  "Square convexity over signed rationals -- the canonical non-trivial convex function.

    signed/square-convex : convex-on (x |-> x*x)
      i.e. ((w0)x + (w1)y)^2 <= (w0)(x*x) + (w1)(y*y)  for w0+w1~1.

  Via the variance identity  csq + w0*w1*(x-y)^2 ~ RHS  (signed/variance-identity),
  whose extra term is nonnegative, so csq <= RHS. The identity is assembled from three
  registered sub-lemmas so that no single kernel check carries the whole reduction cost
  (the monolithic proof exceeded the 1M default budget -- deep multiply-nesting):

    signed/multiply-cross-regroup   : (P*u)*(Q*w) ~ (P*Q)*(u*w)      -- reusable regroup
    signed/square-combination-expand: comb^2 ~ CE (four regrouped monomials)
    signed/variance-term-expand     : w0*w1*(x-y)^2 ~ VE (four signed monomials)
    signed/variance-sum-collapse    : CE + VE ~ RHS (reorder, cancel cross terms, factor)

  Each sub-lemma is opaque once registered, so the identity and square-convex reference
  them at O(1) instead of re-reducing their bodies. Off the magnitude/reciprocal modulus.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-function :as convex-fn]
            [rainbow.math.rational.signed.square-of-sum :as sos]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.matrix.affine-general-rate-certificate :as from-add]
            [rainbow.math.rational.signed.geometric-bridge :as geo-bridge]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]
            [rainbow.math.rational.signed.absolute-multiply :as absolute-multiply]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private sone (function/const* 'signed/one []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sneg [a] (app (function/const* 'signed/negate []) a))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- etr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- massoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mcomm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- mswap [p q r] (app (function/const* 'signed/multiply-swap-outer []) p q r))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- mlre [a b c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) a b c h))
(defn- dleft [f l r] (app (function/const* 'signed/multiply-distributes-add-left []) f l r))
(defn- dright [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- mneg-r [l r] (app (function/const* 'signed/multiply-negate-right []) l r))
(defn- mneg-l [l r] (app (function/const* 'signed/multiply-negate-left []) l r))
(defn- neg-invol [a] (app (function/const* 'signed/negate-involutive []) a))
(defn- negresp [a b h] (app (function/const* 'signed/negate-respects-equivalence []) a b h))
(defn- addresp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- add4 [a b c d] (app (function/const* 'signed/add-four-reorder []) a b c d))
(defn- addzr [a] (app (function/const* 'signed/add-zero-right []) a))
(defn- addcomm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- subself0 [a] (app (function/const* 'signed/subtract-self-equivalent-zero []) a))
(defn- fnn-add [a b] (app (function/const* 'signed/from-nnrat-add []) a b))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- oneleft [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- sos-of [a b] (app (function/const* 'signed/square-of-sum []) a b))
(defn- mult-nn [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- square-nn [v] (app (function/const* 'signed/square-nonnegative []) v))
(defn- addmono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- lerefl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- leresp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most-nnrat [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

;; References to the registered sub-lemmas (opaque once installed).
(defn- xregroup [P u Q w] (app (function/const* 'signed/multiply-cross-regroup []) P u Q w))
(defn- sce-of [w0 w1 x y] (app (function/const* 'signed/square-combination-expand []) w0 w1 x y))
(defn- vte-of [w0 w1 x y] (app (function/const* 'signed/variance-term-expand []) w0 w1 x y))
(defn- vsc-of [w0 w1 x y hw] (app (function/const* 'signed/variance-sum-collapse []) w0 w1 x y hw))
(defn- vid-of [w0 w1 x y hw] (app (function/const* 'signed/variance-identity []) w0 w1 x y hw))

;; a*one ~ a
(defn- one-right [a] (etr (smul a sone) (smul sone a) a (mcomm a sone) (oneleft a)))

;; Common piece builders, parameterized over the four binders (as terms).
(defn- pieces [w0 w1 x y]
  (let [W0 (fnn w0) W1 (fnn w1)
        A (smul W0 x) B (smul W1 y)
        comb (sadd A B) csq (smul comb comb)
        xx (smul x x) yy (smul y y) xy (smul x y) yx (smul y x)
        W00 (smul W0 W0) W01 (smul W0 W1) W10 (smul W1 W0) W11 (smul W1 W1)
        c1 (smul W00 xx) c2 (smul W01 xy) c3 (smul W10 yx) c4 (smul W11 yy)
        v1 (smul W01 xx) v2 (sneg (smul W01 xy)) v3 (sneg (smul W01 yx)) v4 (smul W01 yy)
        dxy (ssub x y) dd (smul dxy dxy)
        var (smul (smul W0 W1) dd)
        CE (sadd (sadd c1 c2) (sadd c3 c4))
        VE (sadd (sadd v1 v2) (sadd v3 v4))
        rhs (sadd (smul W0 xx) (smul W1 yy))]
    {:W0 W0 :W1 W1 :A A :B B :comb comb :csq csq :xx xx :yy yy :xy xy :yx yx
     :W00 W00 :W01 W01 :W10 W10 :W11 W11 :c1 c1 :c2 c2 :c3 c3 :c4 c4
     :v1 v1 :v2 v2 :v3 v3 :v4 v4 :dxy dxy :dd dd :var var :CE CE :VE VE :rhs rhs}))

(def ^:private binders
  [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]])
(def ^:private binders+hw
  (conj binders ['hw (nn-equiv (radd 'w0 'w1) rone)]))

;; ---------------------------------------------------------------------------
;; (P*u)*(Q*w) ~ (P*Q)*(u*w)  -- the reusable monomial regroup.
(def multiply-cross-regroup-spec
  {:name 'signed/multiply-cross-regroup
   :universes []
   :type (function/forall [['P signed] ['u signed] ['Q signed] ['w signed]]
                          (seqv (smul (smul 'P 'u) (smul 'Q 'w))
                                (smul (smul 'P 'Q) (smul 'u 'w))))
   :value
   (function/lam [['P signed] ['u signed] ['Q signed] ['w signed]]
                 (etr (smul (smul 'P 'u) (smul 'Q 'w)) (smul (smul (smul 'P 'u) 'Q) 'w)
                      (smul (smul 'P 'Q) (smul 'u 'w))
                      (esym (smul (smul (smul 'P 'u) 'Q) 'w) (smul (smul 'P 'u) (smul 'Q 'w))
                            (massoc (smul 'P 'u) 'Q 'w))
                      (etr (smul (smul (smul 'P 'u) 'Q) 'w) (smul (smul (smul 'P 'Q) 'u) 'w)
                           (smul (smul 'P 'Q) (smul 'u 'w))
                           (mrre (smul (smul 'P 'u) 'Q) (smul (smul 'P 'Q) 'u) 'w (mswap 'P 'u 'Q))
                           (massoc (smul 'P 'Q) 'u 'w))))})

;; ---------------------------------------------------------------------------
;; comb^2 ~ CE  (square-of-sum, then regroup each of the four monomials).
(def square-combination-expand-spec
  {:name 'signed/square-combination-expand
   :universes []
   :type (function/forall binders
                          (let [{:keys [csq CE]} (pieces 'w0 'w1 'x 'y)] (seqv csq CE)))
   :value
   (function/lam binders
                 (let [{:keys [W0 W1 A B csq xx xy yx yy c1 c2 c3 c4 CE]} (pieces 'w0 'w1 'x 'y)]
                   (etr csq
                        (sadd (sadd (smul A A) (smul A B)) (sadd (smul B A) (smul B B)))
                        CE
                        (sos-of A B)
                        (addresp (sadd (smul A A) (smul A B)) (sadd c1 c2)
                                 (sadd (smul B A) (smul B B)) (sadd c3 c4)
                                 (addresp (smul A A) c1 (smul A B) c2
                                          (xregroup W0 'x W0 'x) (xregroup W0 'x W1 'y))
                                 (addresp (smul B A) c3 (smul B B) c4
                                          (xregroup W1 'y W0 'x) (xregroup W1 'y W1 'y))))))})

;; ---------------------------------------------------------------------------
;; w0*w1*(x-y)^2 ~ VE  (expand the squared difference, distribute w0*w1).
(def variance-term-expand-spec
  {:name 'signed/variance-term-expand
   :universes []
   :type (function/forall binders
                          (let [{:keys [var VE]} (pieces 'w0 'w1 'x 'y)] (seqv var VE)))
   :value
   (function/lam binders
                 (let [{:keys [W0 W1 xx yy xy yx v1 v2 v3 v4 dxy dd var VE W01]} (pieces 'w0 'w1 'x 'y)
                       DE (sadd (sadd xx (sneg xy)) (sadd (sneg yx) yy))
                       negyy (etr (smul (sneg 'y) (sneg 'y)) (sneg (smul 'y (sneg 'y))) yy
                                  (mneg-l 'y (sneg 'y))
                                  (etr (sneg (smul 'y (sneg 'y))) (sneg (sneg yy)) yy
                                       (negresp (smul 'y (sneg 'y)) (sneg yy) (mneg-r 'y 'y))
                                       (neg-invol yy)))
                       dd-DE (etr dd
                                  (sadd (sadd (smul 'x 'x) (smul 'x (sneg 'y)))
                                        (sadd (smul (sneg 'y) 'x) (smul (sneg 'y) (sneg 'y))))
                                  DE
                                  (sos-of 'x (sneg 'y))
                                  (addresp (sadd (smul 'x 'x) (smul 'x (sneg 'y))) (sadd xx (sneg xy))
                                           (sadd (smul (sneg 'y) 'x) (smul (sneg 'y) (sneg 'y)))
                                           (sadd (sneg yx) yy)
                                           (addresp (smul 'x 'x) xx (smul 'x (sneg 'y)) (sneg xy)
                                                    (erefl xx) (mneg-r 'x 'y))
                                           (addresp (smul (sneg 'y) 'x) (sneg yx)
                                                    (smul (sneg 'y) (sneg 'y)) yy
                                                    (mneg-l 'y 'x) negyy)))]
                   (etr var (smul W01 DE) VE
                        (mlre dd DE W01 dd-DE)
                        (etr (smul W01 DE)
                             (sadd (smul W01 (sadd xx (sneg xy))) (smul W01 (sadd (sneg yx) yy)))
                             VE
                             (dleft W01 (sadd xx (sneg xy)) (sadd (sneg yx) yy))
                             (addresp (smul W01 (sadd xx (sneg xy))) (sadd v1 v2)
                                      (smul W01 (sadd (sneg yx) yy)) (sadd v3 v4)
                                      (etr (smul W01 (sadd xx (sneg xy)))
                                           (sadd (smul W01 xx) (smul W01 (sneg xy))) (sadd v1 v2)
                                           (dleft W01 xx (sneg xy))
                                           (addresp (smul W01 xx) v1 (smul W01 (sneg xy)) v2
                                                    (erefl v1) (mneg-r W01 xy)))
                                      (etr (smul W01 (sadd (sneg yx) yy))
                                           (sadd (smul W01 (sneg yx)) (smul W01 yy)) (sadd v3 v4)
                                           (dleft W01 (sneg yx) yy)
                                           (addresp (smul W01 (sneg yx)) v3 (smul W01 yy) v4
                                                    (mneg-r W01 yx) (erefl v4))))))))})

;; ---------------------------------------------------------------------------
;; CE + VE ~ RHS  (reorder to pair c_i+v_i, cancel the cross terms, factor).
(def variance-sum-collapse-spec
  {:name 'signed/variance-sum-collapse
   :universes []
   :type (function/forall binders+hw
                          (let [{:keys [CE VE rhs]} (pieces 'w0 'w1 'x 'y)]
                            (seqv (sadd CE VE) rhs)))
   :value
   (function/lam binders+hw
                 (let [{:keys [W0 W1 xx yy xy yx W00 W01 W10 W11 c1 c2 c3 c4 v1 v2 v3 v4 CE VE rhs]}
                       (pieces 'w0 'w1 'x 'y)
                       wsum1 (etr (sadd W0 W1) (fnn (radd 'w0 'w1)) sone
                                  (fnn-add 'w0 'w1) (fnn-resp (radd 'w0 'w1) rone 'hw))
                       c1v1 (etr (sadd c1 v1) (smul (sadd W00 W01) xx) (smul W0 xx)
                                 (esym (smul (sadd W00 W01) xx) (sadd c1 v1) (dright W00 W01 xx))
                                 (mrre (sadd W00 W01) W0 xx
                                       (etr (sadd W00 W01) (smul W0 (sadd W0 W1)) W0
                                            (esym (smul W0 (sadd W0 W1)) (sadd W00 W01) (dleft W0 W0 W1))
                                            (etr (smul W0 (sadd W0 W1)) (smul W0 sone) W0
                                                 (mlre (sadd W0 W1) sone W0 wsum1)
                                                 (one-right W0)))))
                       c4v4 (etr (sadd c4 v4) (smul (sadd W11 W01) yy) (smul W1 yy)
                                 (esym (smul (sadd W11 W01) yy) (sadd c4 v4) (dright W11 W01 yy))
                                 (mrre (sadd W11 W01) W1 yy
                                       (etr (sadd W11 W01) (smul (sadd W1 W0) W1) W1
                                            (esym (smul (sadd W1 W0) W1) (sadd W11 W01) (dright W1 W0 W1))
                                            (etr (smul (sadd W1 W0) W1) (smul sone W1) W1
                                                 (mrre (sadd W1 W0) sone W1
                                                       (etr (sadd W1 W0) (sadd W0 W1) sone
                                                            (addcomm W1 W0) wsum1))
                                                 (oneleft W1)))))
                       c2v2 (subself0 (smul W01 xy))
                       c3v3 (etr (sadd c3 v3) (sadd (smul W01 yx) v3) szero
                                 (addresp c3 (smul W01 yx) v3 v3 (mrre W10 W01 yx (mcomm W1 W0)) (erefl v3))
                                 (subself0 (smul W01 yx)))
                       paired (etr (sadd CE VE)
                                   (sadd (sadd (sadd c1 c2) (sadd v1 v2)) (sadd (sadd c3 c4) (sadd v3 v4)))
                                   (sadd (sadd (sadd c1 v1) (sadd c2 v2)) (sadd (sadd c3 v3) (sadd c4 v4)))
                                   (add4 (sadd c1 c2) (sadd c3 c4) (sadd v1 v2) (sadd v3 v4))
                                   (addresp (sadd (sadd c1 c2) (sadd v1 v2)) (sadd (sadd c1 v1) (sadd c2 v2))
                                            (sadd (sadd c3 c4) (sadd v3 v4)) (sadd (sadd c3 v3) (sadd c4 v4))
                                            (add4 c1 c2 v1 v2) (add4 c3 c4 v3 v4)))
                       collapsed (addresp (sadd (sadd c1 v1) (sadd c2 v2)) (sadd (smul W0 xx) szero)
                                          (sadd (sadd c3 v3) (sadd c4 v4)) (sadd szero (smul W1 yy))
                                          (addresp (sadd c1 v1) (smul W0 xx) (sadd c2 v2) szero c1v1 c2v2)
                                          (addresp (sadd c3 v3) szero (sadd c4 v4) (smul W1 yy) c3v3 c4v4))
                       cleanup (addresp (sadd (smul W0 xx) szero) (smul W0 xx)
                                        (sadd szero (smul W1 yy)) (smul W1 yy)
                                        (addzr (smul W0 xx))
                                        (etr (sadd szero (smul W1 yy)) (sadd (smul W1 yy) szero) (smul W1 yy)
                                             (addcomm szero (smul W1 yy)) (addzr (smul W1 yy))))]
                   (etr (sadd CE VE)
                        (sadd (sadd (sadd c1 v1) (sadd c2 v2)) (sadd (sadd c3 v3) (sadd c4 v4)))
                        rhs
                        paired
                        (etr (sadd (sadd (sadd c1 v1) (sadd c2 v2)) (sadd (sadd c3 v3) (sadd c4 v4)))
                             (sadd (sadd (smul W0 xx) szero) (sadd szero (smul W1 yy)))
                             rhs collapsed cleanup))))})

;; ---------------------------------------------------------------------------
;; csq + var ~ RHS  (thin assembly over the three opaque sub-lemmas).
(def variance-identity-spec
  {:name 'signed/variance-identity
   :universes []
   :type (function/forall binders+hw
                          (let [{:keys [csq var rhs]} (pieces 'w0 'w1 'x 'y)]
                            (seqv (sadd csq var) rhs)))
   :value
   (function/lam binders+hw
                 (let [{:keys [csq var CE VE rhs]} (pieces 'w0 'w1 'x 'y)]
                   (etr (sadd csq var) (sadd CE VE) rhs
                        (addresp csq CE var VE (sce-of 'w0 'w1 'x 'y) (vte-of 'w0 'w1 'x 'y))
                        (vsc-of 'w0 'w1 'x 'y 'hw))))})

;; ---------------------------------------------------------------------------
;; convex-on (x |-> x*x).
(def square-convex-spec
  {:name 'signed/square-convex
   :universes []
   :type (convex-on (function/lam [['x signed]] (smul 'x 'x)))
   :value
   (function/lam binders+hw
                 (let [{:keys [W0 W1 csq dxy var rhs]} (pieces 'w0 'w1 'x 'y)
                       variance (vid-of 'w0 'w1 'x 'y 'hw)
                       nn-var (mult-nn (smul W0 W1) (smul dxy dxy)
                                       (mult-nn W0 W1 (zero-at-most-nnrat 'w0) (zero-at-most-nnrat 'w1))
                                       (square-nn dxy))
                       step1 (addmono csq csq szero var (lerefl csq) (zle-nn var nn-var))
                       ;; at-most-respects a b c d (a~b)(c~d)(a<=c) : b<=d.
                       ;; use1: a=(csq+0), b=csq, c=(csq+var), d=(csq+var) -> csq <= csq+var
                       use1 (leresp (sadd csq szero) csq (sadd csq var) (sadd csq var)
                                    (addzr csq)
                                    (erefl (sadd csq var)) step1)]
                   ;; final: a=b=csq, c=(csq+var), d=rhs -> csq <= rhs
                   (leresp csq csq (sadd csq var) rhs (erefl csq) variance use1)))})

(def theorem-specs
  [multiply-cross-regroup-spec
   square-combination-expand-spec
   variance-term-expand-spec
   variance-sum-collapse-spec
   variance-identity-spec
   square-convex-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convex-function rainbow.math.rational.signed.square-of-sum rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.distributive rainbow.math.rational.signed.map-sum-algebra rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.rational.signed.geometric-bridge rainbow.math.rational.signed.unit-laws rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.order-respects rainbow.math.linear.vector.norm-nonnegative rainbow.math.rational.signed.absolute-multiply rainbow.math.rational.nnrat.farkas-elim-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-convex theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-convex))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
