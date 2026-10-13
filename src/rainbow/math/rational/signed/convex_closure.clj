(ns rainbow.math.rational.signed.convex-closure
  "Closure properties of signed-rational convexity -- the algebra that makes a convex
  objective composable from convex parts (the convex-optimization bedrock).

    signed/convex-sum         : convex-on f -> convex-on g -> convex-on (x |-> f x + g x)
    signed/convex-nonneg-scale: 0 <= c -> convex-on f -> convex-on (x |-> c * f x)

  Each is the pointwise combination of the two-point inequalities: for w0+w1~1,
  add the two `f`/`g` convexity bounds (add-monotone) then reassociate
  (w0)fx+(w1)fy+(w0)gx+(w1)gy into (w0)(fx+gx)+(w1)(fy+gy) via add-four-reorder and
  multiply-distributes-add-left; scale multiplies the single bound by c>=0
  (multiply-left-monotone) and moves the scalar inside each weighted term
  (a*(W*v) ~ W*(a*v)). Off the magnitude/reciprocal modulus -- no division, so no
  reduction wall (unlike n-point Jensen, whose weight renormalization needs a reciprocal).
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-function :as convex-fn]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-fn (function/arrow signed signed))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- etr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mult-assoc [a b c] (app (function/const* 'signed/multiply-associative []) a b c))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- dist-add-left [f l r] (app (function/const* 'signed/multiply-distributes-add-left []) f l r))
(defn- add-resp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- add-four [a b c d] (app (function/const* 'signed/add-four-reorder []) a b c d))
(defn- add-mono [a ah b bh h1 h2] (app (function/const* 'signed/add-monotone []) a ah b bh h1 h2))
(defn- mult-left-mono [c a b hc hab] (app (function/const* 'signed/multiply-left-monotone []) c a b hc hab))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
;; at-most-respects a ah b bh (a~ah)(b~bh)(a<=b) : ah<=bh  -- result-left is the 2nd arg.
(defn- le-resp [a ah b bh hab hbb hord] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh hab hbb hord))
(defn- mlre [b bh c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) b bh c h))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- max-upper-left [a b] (app (function/const* 'signed/max-upper-left []) a b))
(defn- max-upper-right [a b] (app (function/const* 'signed/max-upper-right []) a b))
(defn- at-most-max [l r u hl hr] (app (function/const* 'signed/at-most-max []) l r u hl hr))
(defn- le-trans [a b c hab hbc] (app (function/const* 'signed/at-most-transitive []) a b c hab hbc))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most-nnrat [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

;; a*(W*v) ~ W*(a*v)
(defn- swap-scalar [a W v]
  (etr (smul a (smul W v)) (smul (smul W a) v) (smul W (smul a v))
       (etr (smul a (smul W v)) (smul (smul a W) v) (smul (smul W a) v)
            (esym (smul (smul a W) v) (smul a (smul W v)) (mult-assoc a W v))
            (mrre (smul a W) (smul W a) v (mult-comm a W)))
       (mult-assoc W a v)))

(defn- wsum [w0 w1 a b] (sadd (smul (fnn w0) a) (smul (fnn w1) b)))

(def convex-sum-spec
  {:name 'signed/convex-sum
   :universes []
   :type (function/forall
          [['f sig-fn] ['g sig-fn] ['cf (convex-on 'f)] ['cg (convex-on 'g)]]
          (convex-on (function/lam [['x signed]] (sadd (app 'f 'x) (app 'g 'x)))))
   :value
   (function/lam
    [['f sig-fn] ['g sig-fn] ['cf (convex-on 'f)] ['cg (convex-on 'g)]]
    (function/lam
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     (let [W0 (fnn 'w0) W1 (fnn 'w1)
           pt (wsum 'w0 'w1 'x 'y)
           fw (app 'f pt) gw (app 'g pt)
           fx (app 'f 'x) fy (app 'f 'y) gx (app 'g 'x) gy (app 'g 'y)
           fB (sadd (smul W0 fx) (smul W1 fy))
           gB (sadd (smul W0 gx) (smul W1 gy))
           cf-inst (app 'cf 'w0 'w1 'x 'y 'hw)     ; fw <= fB
           cg-inst (app 'cg 'w0 'w1 'x 'y 'hw)     ; gw <= gB
           sum-le (add-mono fw fB gw gB cf-inst cg-inst) ; (fw+gw) <= (fB+gB)
           goal-rhs (sadd (smul W0 (sadd fx gx)) (smul W1 (sadd fy gy)))
           ;; (fB+gB) ~ (W0 fx + W0 gx)+(W1 fy + W1 gy) ~ goal-rhs
           bigeq (etr (sadd fB gB)
                      (sadd (sadd (smul W0 fx) (smul W0 gx)) (sadd (smul W1 fy) (smul W1 gy)))
                      goal-rhs
                      (add-four (smul W0 fx) (smul W1 fy) (smul W0 gx) (smul W1 gy))
                      (add-resp (sadd (smul W0 fx) (smul W0 gx)) (smul W0 (sadd fx gx))
                                (sadd (smul W1 fy) (smul W1 gy)) (smul W1 (sadd fy gy))
                                (esym (smul W0 (sadd fx gx)) (sadd (smul W0 fx) (smul W0 gx))
                                      (dist-add-left W0 fx gx))
                                (esym (smul W1 (sadd fy gy)) (sadd (smul W1 fy) (smul W1 gy))
                                      (dist-add-left W1 fy gy))))]
       ;; goal: (fw+gw) <= goal-rhs ; le-resp a ah b bh (a~ah)(b~bh)(a<=b):ah<=bh
       (le-resp (sadd fw gw) (sadd fw gw) (sadd fB gB) goal-rhs
                (erefl (sadd fw gw)) bigeq sum-le))))})

(def convex-nonneg-scale-spec
  {:name 'signed/convex-nonneg-scale
   :universes []
   :type (function/forall
          [['c signed] ['f sig-fn] ['hc (sle szero 'c)] ['cf (convex-on 'f)]]
          (convex-on (function/lam [['x signed]] (smul 'c (app 'f 'x)))))
   :value
   (function/lam
    [['c signed] ['f sig-fn] ['hc (sle szero 'c)] ['cf (convex-on 'f)]]
    (function/lam
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     (let [W0 (fnn 'w0) W1 (fnn 'w1)
           pt (wsum 'w0 'w1 'x 'y)
           fw (app 'f pt) fx (app 'f 'x) fy (app 'f 'y)
           fB (sadd (smul W0 fx) (smul W1 fy))
           cf-inst (app 'cf 'w0 'w1 'x 'y 'hw)      ; fw <= fB
           scaled-le (mult-left-mono 'c fw fB 'hc cf-inst) ; c*fw <= c*fB
           goal-rhs (sadd (smul W0 (smul 'c fx)) (smul W1 (smul 'c fy)))
           ;; c*fB ~ c*(W0 fx) + c*(W1 fy) ~ (W0 (c fx)) + (W1 (c fy)) = goal-rhs
           bigeq (etr (smul 'c fB)
                      (sadd (smul 'c (smul W0 fx)) (smul 'c (smul W1 fy)))
                      goal-rhs
                      (dist-add-left 'c (smul W0 fx) (smul W1 fy))
                      (add-resp (smul 'c (smul W0 fx)) (smul W0 (smul 'c fx))
                                (smul 'c (smul W1 fy)) (smul W1 (smul 'c fy))
                                (swap-scalar 'c W0 fx) (swap-scalar 'c W1 fy)))]
       ;; goal: c*fw <= goal-rhs
       (le-resp (smul 'c fw) (smul 'c fw) (smul 'c fB) goal-rhs
                (erefl (smul 'c fw)) bigeq scaled-le))))})

(def convex-max-spec
  {:name 'signed/convex-max
   :universes []
   :type (function/forall
          [['f sig-fn] ['g sig-fn] ['cf (convex-on 'f)] ['cg (convex-on 'g)]]
          (convex-on (function/lam [['x signed]] (smax (app 'f 'x) (app 'g 'x)))))
   :value
   (function/lam
    [['f sig-fn] ['g sig-fn] ['cf (convex-on 'f)] ['cg (convex-on 'g)]]
    (function/lam
     [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
      ['hw (nn-equiv (radd 'w0 'w1) rone)]]
     (let [W0 (fnn 'w0) W1 (fnn 'w1)
           pt (wsum 'w0 'w1 'x 'y)
           fw (app 'f pt) gw (app 'g pt)
           fx (app 'f 'x) fy (app 'f 'y) gx (app 'g 'x) gy (app 'g 'y)
           mx (smax fx gx) my (smax fy gy)
           rhs (sadd (smul W0 mx) (smul W1 my))
           w0nn (zle-nn W0 (zero-at-most-nnrat 'w0))    ; 0 <= W0
           w1nn (zle-nn W1 (zero-at-most-nnrat 'w1))    ; 0 <= W1
           cf-inst (app 'cf 'w0 'w1 'x 'y 'hw)          ; fw <= W0 fx + W1 fy
           cg-inst (app 'cg 'w0 'w1 'x 'y 'hw)          ; gw <= W0 gx + W1 gy
           ;; each weighted bound is <= the max-weighted rhs (weights >= 0)
           fB-le (add-mono (smul W0 fx) (smul W0 mx) (smul W1 fy) (smul W1 my)
                           (mult-left-mono W0 fx mx w0nn (max-upper-left fx gx))
                           (mult-left-mono W1 fy my w1nn (max-upper-left fy gy)))
           gB-le (add-mono (smul W0 gx) (smul W0 mx) (smul W1 gy) (smul W1 my)
                           (mult-left-mono W0 gx mx w0nn (max-upper-right fx gx))
                           (mult-left-mono W1 gy my w1nn (max-upper-right fy gy)))
           fw-le (le-trans fw (sadd (smul W0 fx) (smul W1 fy)) rhs cf-inst fB-le)
           gw-le (le-trans gw (sadd (smul W0 gx) (smul W1 gy)) rhs cg-inst gB-le)]
       ;; max(fw,gw) <= rhs since both fw,gw <= rhs
       (at-most-max fw gw rhs fw-le gw-le))))})

(def theorem-specs [convex-sum-spec convex-nonneg-scale-spec convex-max-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex-fn/extend-environment
      distributive/extend-environment
      action-scale/extend-environment
      multiply-associative/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      multiply-monotone/extend-environment
      order-monotone/extend-environment
      order-transitivity/extend-environment
      order-respects/extend-environment
      minmax/extend-environment
      farkas/extend-environment
      (support/extend-with :signed-convex-closure theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
