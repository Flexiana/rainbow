(ns rainbow.math.rational.signed.square-of-sum
  "The four-term expansion of a squared sum over signed rationals -- a reusable step for
  square convexity (the variance inequality) and other quadratic identities.

    signed/square-of-sum : (a+b)*(a+b) ~ ((a*a) + (a*b)) + ((b*a) + (b*b))

  One right-distribution then two left-distributions. (a*b and b*a are kept distinct since
  the caller decides when to commute.) Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- dist-add-right [a b m] (app (function/const* 'signed/multiply-distributes-add-right []) a b m))
(defn- dist-add-left [f l r] (app (function/const* 'signed/multiply-distributes-add-left []) f l r))
(defn- add-resp [a ah b bh ha hb] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh ha hb))

(def square-of-sum-spec
  {:name 'signed/square-of-sum
   :universes []
   :type (function/forall
          [['a signed] ['b signed]]
          (seqv (smul (sadd 'a 'b) (sadd 'a 'b))
                (sadd (sadd (smul 'a 'a) (smul 'a 'b))
                      (sadd (smul 'b 'a) (smul 'b 'b)))))
   :value
   (function/lam
    [['a signed] ['b signed]]
    (let [s (sadd 'a 'b)]
      (eqv-tr (smul s s)
              (sadd (smul 'a s) (smul 'b s))
              (sadd (sadd (smul 'a 'a) (smul 'a 'b)) (sadd (smul 'b 'a) (smul 'b 'b)))
              (dist-add-right 'a 'b s)
              (add-resp (smul 'a s) (sadd (smul 'a 'a) (smul 'a 'b))
                        (smul 'b s) (sadd (smul 'b 'a) (smul 'b 'b))
                        (dist-add-left 'a 'a 'b)
                        (dist-add-left 'b 'a 'b)))))})

(def theorem-specs [square-of-sum-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.equivalence-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-of-sum theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-of-sum))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
