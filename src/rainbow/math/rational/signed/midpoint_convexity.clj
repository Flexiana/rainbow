(ns rainbow.math.rational.signed.midpoint-convexity
  "Midpoint convexity over signed rationals: the midpoint stays in [min, max].

    signed/midpoint-at-most-max  : (1/2)*v0 + (1/2)*v1 <= max v0 v1
    signed/midpoint-at-least-min : min v0 v1 <= (1/2)*v0 + (1/2)*v1

  where (1/2)*v = smul (from-nnrat nnrat/half) v. The w0=w1=1/2 case of the two-point
  convex combination -- but proved directly via signed/half-scale-add-self (1/2 M + 1/2 M
  ~ M), so it needs no nnrat weight-sum equality. Each 1/2*v_i <= 1/2*(max) by
  multiply-left-monotone (1/2 = from-nnrat nnrat/half >= 0, v_i <= max); sum; collapse
  1/2 M + 1/2 M ~ M. Off the magnitude/reciprocal modulus (no reduction wall). Axiom-free;
  additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness :as half-row]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private signed-half
  (function/app (function/const* 'signed/from-nnrat []) (function/const* 'nnrat/half [])))
(def ^:private nnrat-half (function/const* 'nnrat/half []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- smin [a b] (app (function/const* 'signed/min []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- mult-left-mono [c a b hc hab] (app (function/const* 'signed/multiply-left-monotone []) c a b hc hab))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- half-add-self [v] (app (function/const* 'signed/half-scale-add-self []) v))
(defn- max-upper-left [a b] (app (function/const* 'signed/max-upper-left []) a b))
(defn- max-upper-right [a b] (app (function/const* 'signed/max-upper-right []) a b))
(defn- min-lower-left [a b] (app (function/const* 'signed/min-lower-left []) a b))
(defn- min-lower-right [a b] (app (function/const* 'signed/min-lower-right []) a b))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- zle-of-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most [q] (app (function/const* 'nnrat/zero-at-most []) q))
(def ^:private half-nonneg (zle-of-nn signed-half (zero-at-most nnrat-half)))  ; 0 <= 1/2
(defn- midpoint [v0 v1] (sadd (smul signed-half v0) (smul signed-half v1)))

(def midpoint-at-most-max-spec
  {:name 'signed/midpoint-at-most-max
   :universes []
   :type (function/forall [['v0 signed] ['v1 signed]]
                          (sle (midpoint 'v0 'v1) (smax 'v0 'v1)))
   :value
   (function/lam
    [['v0 signed] ['v1 signed]]
    (let [M (smax 'v0 'v1)
          bounded (add-mono (smul signed-half 'v0) (smul signed-half M)
                            (smul signed-half 'v1) (smul signed-half M)
                            (mult-left-mono signed-half 'v0 M half-nonneg (max-upper-left 'v0 'v1))
                            (mult-left-mono signed-half 'v1 M half-nonneg (max-upper-right 'v0 'v1)))]
      (le-resp (midpoint 'v0 'v1) (midpoint 'v0 'v1)
               (sadd (smul signed-half M) (smul signed-half M)) M
               (erefl (midpoint 'v0 'v1)) (half-add-self M) bounded)))})

(def midpoint-at-least-min-spec
  {:name 'signed/midpoint-at-least-min
   :universes []
   :type (function/forall [['v0 signed] ['v1 signed]]
                          (sle (smin 'v0 'v1) (midpoint 'v0 'v1)))
   :value
   (function/lam
    [['v0 signed] ['v1 signed]]
    (let [m (smin 'v0 'v1)
          bounded (add-mono (smul signed-half m) (smul signed-half 'v0)
                            (smul signed-half m) (smul signed-half 'v1)
                            (mult-left-mono signed-half m 'v0 half-nonneg (min-lower-left 'v0 'v1))
                            (mult-left-mono signed-half m 'v1 half-nonneg (min-lower-right 'v0 'v1)))]
      (le-resp (sadd (smul signed-half m) (smul signed-half m)) m
               (midpoint 'v0 'v1) (midpoint 'v0 'v1)
               (half-add-self m) (erefl (midpoint 'v0 'v1)) bounded)))})

(def theorem-specs [midpoint-at-most-max-spec midpoint-at-least-min-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.minmax rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.order-monotone rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.order-respects rainbow.math.rational.nnrat.farkas-elim-list])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-midpoint-convexity theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.midpoint-convexity))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
