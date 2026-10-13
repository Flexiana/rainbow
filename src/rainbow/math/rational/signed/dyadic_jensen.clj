(ns rainbow.math.rational.signed.dyadic-jensen
  "Dyadic (four-point) Jensen for signed-rational convex functions -- n-point Jensen for the
  power-of-two case, reachable WITHOUT the reciprocal wall that blocks general n-point Jensen
  (which needs weight renormalization by 1/(1-w0)). Uses only halving (w=1/2), so it iterates
  two-point convexity through nested midpoints.

    nnrat/half-add-self-equivalent-one : 1/2 + 1/2 ~ 1
    signed/dyadic-jensen-four :
      convex-on f ->
      f(mid(mid x0 x1)(mid x2 x3)) <= mid(mid (f x0)(f x1))(mid (f x2)(f x3))
      where mid a b = (1/2)a + (1/2)b.

  f is abstract, so the type stays cheap to check (f stuck at the combination). Proof: apply
  convex-on at (1/2,1/2) to each midpoint (bounding f of a midpoint by the midpoint of f's),
  then combine by midpoint monotonicity and transitivity. Wall-free; does not touch the LP
  checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-function :as convex-fn]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private type-level [:succ [:zero]])
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-fn (function/arrow signed signed))
(def ^:private nnrat-half (function/const* 'nnrat/half []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- mult-left-mono [c a b hc hab] (app (function/const* 'signed/multiply-left-monotone []) c a b hc hab))
(defn- add-mono [a ah b bh h1 h2] (app (function/const* 'signed/add-monotone []) a ah b bh h1 h2))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most-nnrat [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

(def ^:private sig-half (fnn nnrat-half))
(defn- mid [a b] (sadd (smul sig-half a) (smul sig-half b)))
(def ^:private half-nonneg (zle-nn sig-half (zero-at-most-nnrat nnrat-half)))   ; 0 <= 1/2

;; 1/2 + 1/2 ~ 1, by reflexivity of the cross-product (num(1/2+1/2)*den(1) ~ num(1)*den(1/2+1/2)).
(def half-add-self-equivalent-one-spec
  {:name 'nnrat/half-add-self-equivalent-one
   :universes []
   :type (nn-equiv (radd nnrat-half nnrat-half) rone)
   :value (app (function/const* 'equality/reflexive [type-level])
               (function/const* 'data/Nat [])
               (app (function/const* 'nat/multiply [])
                    (app (function/const* 'nnrat/numerator []) (radd nnrat-half nnrat-half))
                    (app (function/const* 'nnrat/denominator []) rone)))})

(def ^:private hw (function/const* 'nnrat/half-add-self-equivalent-one []))

;; convex-on f at (1/2,1/2,a,b) : f(mid a b) <= mid (f a)(f b)
(defn- cvx [cf a b] (app cf nnrat-half nnrat-half a b hw))

(def dyadic-jensen-four-spec
  {:name 'signed/dyadic-jensen-four
   :universes []
   :type (function/forall
          [['f sig-fn] ['cf (convex-on 'f)]
           ['x0 signed] ['x1 signed] ['x2 signed] ['x3 signed]]
          (sle (app 'f (mid (mid 'x0 'x1) (mid 'x2 'x3)))
               (mid (mid (app 'f 'x0) (app 'f 'x1)) (mid (app 'f 'x2) (app 'f 'x3)))))
   :value
   (function/lam
    [['f sig-fn] ['cf (convex-on 'f)]
     ['x0 signed] ['x1 signed] ['x2 signed] ['x3 signed]]
    (let [m01 (mid 'x0 'x1) m23 (mid 'x2 'x3) M (mid m01 m23)
          fx0 (app 'f 'x0) fx1 (app 'f 'x1) fx2 (app 'f 'x2) fx3 (app 'f 'x3)
          fm01 (app 'f m01) fm23 (app 'f m23)
          B01 (mid fx0 fx1) B23 (mid fx2 fx3)
          c01 (cvx 'cf 'x0 'x1)     ; fm01 <= B01
          c23 (cvx 'cf 'x2 'x3)     ; fm23 <= B23
          cM  (cvx 'cf m01 m23)     ; f(M) <= mid fm01 fm23
          ;; midpoint monotonicity: mid fm01 fm23 <= mid B01 B23
          mono (add-mono (smul sig-half fm01) (smul sig-half B01)
                         (smul sig-half fm23) (smul sig-half B23)
                         (mult-left-mono sig-half fm01 B01 half-nonneg c01)
                         (mult-left-mono sig-half fm23 B23 half-nonneg c23))]
      (le-trans (app 'f M) (mid fm01 fm23) (mid B01 B23) cM mono)))})

(def theorem-specs [half-add-self-equivalent-one-spec dyadic-jensen-four-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convex-function rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.multiply-order rainbow.math.rational.nnrat.farkas-elim-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-dyadic-jensen theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.dyadic-jensen))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
