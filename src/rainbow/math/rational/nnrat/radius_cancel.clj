(ns rainbow.math.rational.nnrat.radius-cancel
  "The reciprocal radius-cancellation for a general positive nnrat, the linchpin of the
  limit-product modulus.

    analysis/nnrat-radius-cancel :
      1 <= numerator D  ->
      (from-nnrat D) * ((from-nnrat (recip (make (succ (pred (num D))) (den-pred D)))) * eps) ~ eps

  Everything is kept in the make(succ p, q) form mmag := make(succ(pred(num D)))(den-pred D)
  (so analysis/scale-reciprocal-radius-cancel from the limit-scale work applies directly),
  and D ~ mmag (nnrat/make-succ-of-positive-numerator) is lifted to from-nnrat D ~ from-nnrat
  mmag (from-nnrat-respects-equivalence) then under the scale (multiply-right-respects).
  No nnrat/reciprocal-respects needed. Axiom-free; additive."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-scale-law :as scale-law]
            [rainbow.math.rational.nnrat.positive-succ-form :as succ-form]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- mk [num denpred] (app (function/const* 'data/pair [tl tl]) nat nat num denpred))
(defn- recip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- fnn-resp [a b h] (app (function/const* 'signed/from-nnrat-respects-equivalence []) a b h))
(defn- make-succ [c h] (app (function/const* 'nnrat/make-succ-of-positive-numerator []) c h))
(defn- src [p q d] (app (function/const* 'analysis/scale-reciprocal-radius-cancel []) p q d))

(def nnrat-radius-cancel-spec
  {:name 'analysis/nnrat-radius-cancel
   :universes []
   :type (function/forall [['D nnrat] ['eps signed] ['h (nat-le (succ (function/const* 'data/zero [])) (numr 'D))]]
                          (let [mmag (mk (succ (pred* (numr 'D))) (denpred 'D))]
                            (seqv (smul (fnn 'D) (smul (fnn (recip mmag)) 'eps)) 'eps)))
   :value
   (function/lam [['D nnrat] ['eps signed] ['h (nat-le (succ (function/const* 'data/zero [])) (numr 'D))]]
                 (let [mmag (mk (succ (pred* (numr 'D))) (denpred 'D))
                       inner (smul (fnn (recip mmag)) 'eps)
                       core (src (pred* (numr 'D)) (denpred 'D) 'eps)      ; smul(from-nnrat mmag) inner ~ eps
                       Dmm (make-succ 'D 'h)                               ; D ~ mmag (nnrat)
                       bridge (mrre (fnn 'D) (fnn mmag) inner (fnn-resp 'D mmag Dmm))]  ; smul(from-nnrat D) inner ~ smul(from-nnrat mmag) inner
                   (eqv-tr (smul (fnn 'D) inner) (smul (fnn mmag) inner) 'eps bridge core)))})

(def theorem-specs [nnrat-radius-cancel-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.limit-scale-law rainbow.math.rational.nnrat.positive-succ-form rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-radius-cancel theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.radius-cancel))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
