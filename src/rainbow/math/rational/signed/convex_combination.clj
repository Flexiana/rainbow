(ns rainbow.math.rational.signed.convex-combination
  "Two-point convex combination of signed rationals stays within [min, max] -- the signed
  lift of nnrat/convex-at-most-max / convex-at-least-min, and a foundation brick for
  convex optimization over signed rationals (connects to the KKT / Lagrangian lane).

    signed/convex-at-most-max :
      (w0 + w1 ~ 1) -> (from-nnrat w0)*v0 + (from-nnrat w1)*v1 <= max v0 v1
    signed/convex-at-least-min :
      (w0 + w1 ~ 1) -> min v0 v1 <= (from-nnrat w0)*v0 + (from-nnrat w1)*v1

  Weights are nonnegative (nnrat, injected by from-nnrat). Each w_i*v_i is bounded by
  w_i*max (multiply-left-monotone, weight >= 0, v_i <= max), the two sum, and the weight
  sum collapses (w0+w1)*max ~ 1*max ~ max via distributivity + from-nnrat-add + (w0+w1~1).
  Does NOT route through the magnitude/reciprocal modulus, so it is free of that reduction
  wall. Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.affine-general-rate-certificate :as from-add]
            [rainbow.math.rational.signed.geometric-bridge :as geo-bridge]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- smax [a b] (app (function/const* 'signed/max []) a b))
(defn- smin [a b] (app (function/const* 'signed/min []) a b))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- mult-left-mono [c a b hc hab] (app (function/const* 'signed/multiply-left-monotone []) c a b hc hab))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- dist-add-right [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- fnn-add [a b] (app (function/const* 'signed/from-nnrat-add []) a b))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- one-left [z] (app (function/const* 'signed/multiply-one-left []) z))
(defn- max-upper-left [a b] (app (function/const* 'signed/max-upper-left []) a b))
(defn- max-upper-right [a b] (app (function/const* 'signed/max-upper-right []) a b))
(defn- min-lower-left [a b] (app (function/const* 'signed/min-lower-left []) a b))
(defn- min-lower-right [a b] (app (function/const* 'signed/min-lower-right []) a b))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- zle-of-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- fnn-nonneg-zle [w] (zle-of-nn (fnn w) (zero-at-most w)))  ; 0 <= from-nnrat w

(defn- wsum [w0 w1 v0 v1] (sadd (smul (fnn w0) v0) (smul (fnn w1) v1)))
;; sadd (w0*B)(w1*B) ~ B, given w0+w1 ~ 1  (B = the bound, max or min)
(defn- weights-collapse [w0 w1 B hw]
  (eqv-tr (sadd (smul (fnn w0) B) (smul (fnn w1) B)) (smul (fnn (radd w0 w1)) B) B
          ;; (w0*B)+(w1*B) ~ (w0+w1)*B ~ ((w0+w1) as one)*B
          (eqv-tr (sadd (smul (fnn w0) B) (smul (fnn w1) B))
                  (smul (sadd (fnn w0) (fnn w1)) B) (smul (fnn (radd w0 w1)) B)
                  (eqv-sym (smul (sadd (fnn w0) (fnn w1)) B)
                           (sadd (smul (fnn w0) B) (smul (fnn w1) B))
                           (dist-add-right (fnn w0) (fnn w1) B))
                  (mrre (sadd (fnn w0) (fnn w1)) (fnn (radd w0 w1)) B (fnn-add w0 w1)))
          ;; (w0+w1)*B ~ 1*B ~ B
          (eqv-tr (smul (fnn (radd w0 w1)) B) (smul (fnn rone) B) B
                  (mrre (fnn (radd w0 w1)) (fnn rone) B (fnn-resp (radd w0 w1) rone hw))
                  (one-left B))))

(def convex-at-most-max-spec
  {:name 'signed/convex-at-most-max
   :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 signed] ['v1 signed]
           ['hw (nn-equiv (radd 'w0 'w1) rone)]]
          (sle (wsum 'w0 'w1 'v0 'v1) (smax 'v0 'v1)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 signed] ['v1 signed]
     ['hw (nn-equiv (radd 'w0 'w1) rone)]]
    (let [M (smax 'v0 'v1)
          bounded (add-mono (smul (fnn 'w0) 'v0) (smul (fnn 'w0) M)
                            (smul (fnn 'w1) 'v1) (smul (fnn 'w1) M)
                            (mult-left-mono (fnn 'w0) 'v0 M (fnn-nonneg-zle 'w0) (max-upper-left 'v0 'v1))
                            (mult-left-mono (fnn 'w1) 'v1 M (fnn-nonneg-zle 'w1) (max-upper-right 'v0 'v1)))]
      (le-resp (wsum 'w0 'w1 'v0 'v1) (wsum 'w0 'w1 'v0 'v1)
               (sadd (smul (fnn 'w0) M) (smul (fnn 'w1) M)) M
               (erefl (wsum 'w0 'w1 'v0 'v1)) (weights-collapse 'w0 'w1 M 'hw) bounded)))})

(def convex-at-least-min-spec
  {:name 'signed/convex-at-least-min
   :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 signed] ['v1 signed]
           ['hw (nn-equiv (radd 'w0 'w1) rone)]]
          (sle (smin 'v0 'v1) (wsum 'w0 'w1 'v0 'v1)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 signed] ['v1 signed]
     ['hw (nn-equiv (radd 'w0 'w1) rone)]]
    (let [m (smin 'v0 'v1)
          bounded (add-mono (smul (fnn 'w0) m) (smul (fnn 'w0) 'v0)
                            (smul (fnn 'w1) m) (smul (fnn 'w1) 'v1)
                            (mult-left-mono (fnn 'w0) m 'v0 (fnn-nonneg-zle 'w0) (min-lower-left 'v0 'v1))
                            (mult-left-mono (fnn 'w1) m 'v1 (fnn-nonneg-zle 'w1) (min-lower-right 'v0 'v1)))]
      ;; m ~ (w0*m)+(w1*m) <= wsum
      (le-resp (sadd (smul (fnn 'w0) m) (smul (fnn 'w1) m)) m
               (wsum 'w0 'w1 'v0 'v1) (wsum 'w0 'w1 'v0 'v1)
               (weights-collapse 'w0 'w1 m 'hw) (erefl (wsum 'w0 'w1 'v0 'v1)) bounded)))})

(def theorem-specs [convex-at-most-max-spec convex-at-least-min-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      minmax/extend-environment
      multiply-monotone/extend-environment
      order-monotone/extend-environment
      distributive/extend-environment
      from-add/extend-environment
      geo-bridge/extend-environment
      multiply-ring/extend-environment
      unit-laws/extend-environment
      multiply-order/extend-environment
      order-respects/extend-environment
      farkas/extend-environment
      (support/extend-with :signed-convex-combination theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
