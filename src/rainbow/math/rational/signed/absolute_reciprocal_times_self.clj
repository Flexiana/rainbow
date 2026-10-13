(ns rainbow.math.rational.signed.absolute-reciprocal-times-self
  "B6f prerequisite: the multiplicative absolute reciprocal identity.

    signed/absolute-reciprocal-times-self :
      1 <= num(mag(x*x)) -> |reciprocal x| * |x| ~ 1

  This is the clean building block for the limit-reciprocal assembly's constant bound on
  |reciprocal (s n)|. Unlike the additive |1/x| ~ 1/|x| (which crosses magnitude
  representatives and hits the absent reciprocal-respects lemma), this multiplicative form
  stays representative-free: |1/x|*|x| ~ |x*(1/x)| ~ |1| ~ 1 via absolute-multiply +
  multiply-reciprocal-self + |1|~1. In the assembly, combined with |s n| >= |L|/2 and
  multiply-right-cancel, it yields |reciprocal (s n)| <= reciprocal(|L|/2) = 2/|L|.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.reciprocal :as reciprocal]
            [rainbow.math.rational.signed.absolute-multiply :as absolute-multiply]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.rational.signed.absolute-algebra :as absolute-algebra]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]))

(def ^:private tl [:succ [:zero]])
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private zero (function/const* 'data/zero []))
(def ^:private one (function/const* 'signed/one []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- mag [x] (app (function/const* 'signed/magnitude []) x))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- reciprocal [x] (app (function/const* 'signed/reciprocal []) x))
(defn- eqv-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- eqv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- abs-mul [a b] (app (function/const* 'signed/absolute-multiply []) a b))
(defn- abs-resp [a b h] (app (function/const* 'signed/absolute-respects-equivalence []) a b h))
(defn- abs-of-nn [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- self-inv [x h] (app (function/const* 'signed/multiply-reciprocal-self []) x h))
(def ^:private zero-le-one (function/const* 'signed/zero-at-most-one []))

(def absolute-reciprocal-times-self-spec
  {:name 'signed/absolute-reciprocal-times-self
   :universes []
   :type (function/forall
          [['x signed] ['h (nat-le (succ zero) (numr (mag (smul 'x 'x))))]]
          (seqv (smul (abs* (reciprocal 'x)) (abs* 'x)) one))
   :value
   (function/lam
    [['x signed] ['h (nat-le (succ zero) (numr (mag (smul 'x 'x))))]]
    (let [rx (reciprocal 'x)
          x*rx (smul 'x rx)]
      ;; |rx|*|x| ~ |x|*|rx| ~ |x*rx| ~ |1| ~ 1
      (eqv-tr (smul (abs* rx) (abs* 'x)) (smul (abs* 'x) (abs* rx)) one
              (mult-comm (abs* rx) (abs* 'x))
              (eqv-tr (smul (abs* 'x) (abs* rx)) (abs* x*rx) one
                      (eqv-sym (abs* x*rx) (smul (abs* 'x) (abs* rx)) (abs-mul 'x rx))
                      (eqv-tr (abs* x*rx) (abs* one) one
                              (abs-resp x*rx one (self-inv 'x 'h))
                              (abs-of-nn one zero-le-one))))))})

(def theorem-specs [absolute-reciprocal-times-self-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      reciprocal/extend-environment
      absolute-multiply/extend-environment
      absolute-sign/extend-environment
      absolute-algebra/extend-environment
      multiply-ring/extend-environment
      unit-laws/extend-environment
      (support/extend-with :signed-absolute-reciprocal-times-self theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
