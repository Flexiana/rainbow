(ns rainbow.math.rational.signed.reciprocal-nonnegative
  "B3 of the limit-reciprocal arc: the reciprocal of a nonnegative signed rational is
  nonnegative.

    signed/reciprocal-nonnegative : nonnegative x -> nonnegative (reciprocal x)

  Immediate from the sign-free definition reciprocal x = x * (1/(x*x)): the second factor
  1/(x*x) = from-nnrat (recip mmag) is nonnegative (from-nnrat of any nnrat is >= 0, since
  its negative component is 0 -- nnrat/zero-at-most), so multiply-nonnegative closes it.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.reciprocal :as reciprocal]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.nnrat.farkas-elim-list :as farkas]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- pred* [n] (app (function/const* 'nat/predecessor []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- fnn [q] (app (function/const* 'signed/from-nnrat []) q))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- mk [num dp] (app (function/const* 'data/pair [tl tl]) nat nat num dp))
(defn- nrecip [x] (app (function/const* 'nnrat/reciprocal []) x))
(defn- nonneg [x] (app (function/const* 'signed/nonnegative []) x))
(defn- reciprocal [x] (app (function/const* 'signed/reciprocal []) x))
(defn- mult-nn [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- zero-at-most [q] (app (function/const* 'nnrat/zero-at-most []) q))

(def reciprocal-nonnegative-spec
  {:name 'signed/reciprocal-nonnegative
   :universes []
   :type (function/forall [['x signed] ['hx (nonneg 'x)]]
                          (nonneg (reciprocal 'x)))
   :value
   (function/lam [['x signed] ['hx (nonneg 'x)]]
                 (let [rq (nrecip (mk (succ (pred* (numr (mag (smul 'x 'x))))) (denpred (mag (smul 'x 'x)))))
                       R (fnn rq)]
                   ;; nonneg R  =def=  nnrat/at-most 0 rq  =  zero-at-most rq
                   (mult-nn 'x R 'hx (zero-at-most rq))))})

(def theorem-specs [reciprocal-nonnegative-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      reciprocal/extend-environment
      multiply-order/extend-environment
      farkas/extend-environment
      (support/extend-with :signed-reciprocal-nonnegative theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
