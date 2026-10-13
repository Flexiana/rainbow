(ns rainbow.math.rational.signed.absolute-convex
  "Absolute value is convex -- the canonical non-smooth convex function, the basis of
  L1 / robust / minimax objectives.

    signed/absolute-convex : convex-on (x |-> |x|)
      i.e. |(w0)x + (w1)y| <= (w0)|x| + (w1)|y|  for w0+w1~1.

  The triangle inequality bounds |(w0)x + (w1)y| by |(w0)x| + |(w1)y|; each term rewrites
  via |a*b| ~ |a|*|b| and |from-nnrat w| ~ from-nnrat w (weights are nonnegative) to
  (w0)|x| + (w1)|y|. Wall-free (no reciprocal); does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convex-function :as convex-fn]
            [rainbow.math.rational.signed.absolute :as absolute]
            [rainbow.math.rational.signed.distance-triangle :as triangle]
            [rainbow.math.rational.signed.absolute-multiply :as abs-multiply]
            [rainbow.math.rational.signed.absolute-sign :as abs-sign]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private rone (function/const* 'nnrat/one []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sabs [a] (app (function/const* 'signed/absolute []) a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nn-equiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- etr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- add-resp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))
(defn- le-resp [a ah b bh hab hbb hord] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh hab hbb hord))
(defn- abs-add-triangle [a b] (app (function/const* 'signed/absolute-add-triangle []) a b))
(defn- abs-multiply [a b] (app (function/const* 'signed/absolute-multiply []) a b))
(defn- abs-of-nonneg [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- zero-at-most-nnrat [q] (app (function/const* 'nnrat/zero-at-most []) q))
(defn- convex-on [f] (app (function/const* 'signed/convex-on []) f))

;; |W*v| ~ W*|v|  for W = from-nnrat w (nonnegative)
(defn- abs-weight [w v]
  (let [W (fnn w)]
    (etr (sabs (smul W v)) (smul (sabs W) (sabs v)) (smul W (sabs v))
         (abs-multiply W v)
         (mrre (sabs W) W (sabs v) (abs-of-nonneg W (zle-nn W (zero-at-most-nnrat w)))))))

(def absolute-convex-spec
  {:name 'signed/absolute-convex
   :universes []
   :type (convex-on (function/lam [['x signed]] (sabs 'x)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['x signed] ['y signed]
     ['hw (nn-equiv (radd 'w0 'w1) rone)]]
    (let [W0 (fnn 'w0) W1 (fnn 'w1)
          A (smul W0 'x) B (smul W1 'y)
          comb (sadd A B)
          rhs (sadd (smul W0 (sabs 'x)) (smul W1 (sabs 'y)))
          tri (abs-add-triangle A B)                       ; |comb| <= |A| + |B|
          rewrite (add-resp (sabs A) (smul W0 (sabs 'x)) (sabs B) (smul W1 (sabs 'y))
                            (abs-weight 'w0 'x) (abs-weight 'w1 'y))] ; |A|+|B| ~ rhs
      (le-resp (sabs comb) (sabs comb) (sadd (sabs A) (sabs B)) rhs
               (erefl (sabs comb)) rewrite tri)))})

(def theorem-specs [absolute-convex-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex-fn/extend-environment
      absolute/extend-environment
      triangle/extend-environment
      abs-multiply/extend-environment
      abs-sign/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      multiply-order/extend-environment
      order-respects/extend-environment
      farkas/extend-environment
      (support/extend-with :signed-absolute-convex theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
