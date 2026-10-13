(ns rainbow.math.rational.signed.multiply-positive
  "signed/multiply-positive : 0 < a -> 0 < b -> 0 < a*b. From 0<a extract 0<=a and not(0~a)
  (less-than is the reducible conjunction of the two); a*b is nonnegative (multiply-nonnegative)
  and nonzero (multiply-nonzero applied to the distinctness facts), so less-than-intro gives
  0 < a*b. The strict-positivity payoff of the general no-zero-divisors chain -- feeds the
  strict-convexity capstone (0 < w0*w1*(x-y)^2)."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-nonzero :as nonzero]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.strict-order :as strict-order]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- slt [a b] (app (function/const* 'signed/less-than []) a b))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))
(defn- s-esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- lt-intro [x y le neq] (app (function/const* 'signed/less-than-intro []) x y le neq))
(defn- lt-at-most [x y h] (app (function/const* 'signed/less-than-implies-at-most []) x y h))
(defn- mult-nonneg [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- mult-nonzero [a b ha hb] (app (function/const* 'signed/multiply-nonzero []) a b ha hb))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- nonneg-of-0le [x h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) x h))
(defn- zle-of-nonneg [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))

;; From h : 0 < x  (defeq conjunction (0<=x) (not(0~x)))  derive  not(x ~ 0).
(defn- distinct-from-zero [x h]
  (function/lam [['z (seqv x szero)]]
                (app (pright (sle szero x) (pneg (seqv szero x)) h)
                     (s-esym x szero 'z))))

(def multiply-positive-spec
  {:name 'signed/multiply-positive
   :universes []
   :type (function/forall [['a signed] ['b signed]
                           ['ha (slt szero 'a)] ['hb (slt szero 'b)]]
                          (slt szero (smul 'a 'b)))
   :value
   (function/lam
    [['a signed] ['b signed] ['ha (slt szero 'a)] ['hb (slt szero 'b)]]
    (lt-intro szero (smul 'a 'b)
              (zle-of-nonneg (smul 'a 'b)                                              ; 0 <= a*b
                             (mult-nonneg 'a 'b
                                          (nonneg-of-0le 'a (lt-at-most szero 'a 'ha))
                                          (nonneg-of-0le 'b (lt-at-most szero 'b 'hb))))
              (function/lam [['h (seqv szero (smul 'a 'b))]]                           ; not(0 ~ a*b)
                            (app (mult-nonzero 'a 'b (distinct-from-zero 'a 'ha) (distinct-from-zero 'b 'hb))
                                 (s-esym szero (smul 'a 'b) 'h)))))})

(def theorem-specs [multiply-positive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      nonzero/extend-environment
      multiply-order/extend-environment
      strict-order/extend-environment
      (support/extend-with :signed-multiply-positive theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
