(ns rainbow.math.rational.signed.square-monotone
  "B6b of the limit-reciprocal arc: squaring is monotone on nonnegatives.

    signed/square-monotone : 0 <= a -> a <= b -> a*a <= b*b

  Two applications of multiply-right-monotone: a*a <= b*a (multiply a<=b by a>=0) and
  a*b <= b*b (multiply a<=b by b>=0, where 0<=b from 0<=a<=b); align b*a ~ a*b by
  commutativity and chain by transitivity. Feeds the assembly's positivity derivation
  (with magnitude-monotone: |L|/2 <= |s n| -> (|L|/2)^2 <= (s n)^2 -> mag positive).
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- mult-right-mono [c a b hc hab] (app (function/const* 'signed/multiply-right-monotone []) c a b hc hab))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- mult-comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))

(def square-monotone-spec
  {:name 'signed/square-monotone
   :universes []
   :type (function/forall
          [['a signed] ['b signed] ['ha (sle szero 'a)] ['hab (sle 'a 'b)]]
          (sle (smul 'a 'a) (smul 'b 'b)))
   :value
   (function/lam
    [['a signed] ['b signed] ['ha (sle szero 'a)] ['hab (sle 'a 'b)]]
    (let [zb (le-trans szero 'a 'b 'ha 'hab)                        ; 0 <= b
          s1 (mult-right-mono 'a 'a 'b 'ha 'hab)                    ; a*a <= b*a
          s2 (mult-right-mono 'b 'a 'b zb 'hab)                     ; a*b <= b*b
          ba<=bb (le-resp (smul 'a 'b) (smul 'b 'a) (smul 'b 'b) (smul 'b 'b)
                          (mult-comm 'a 'b) (erefl (smul 'b 'b)) s2)]  ; b*a <= b*b
      (le-trans (smul 'a 'a) (smul 'b 'a) (smul 'b 'b) s1 ba<=bb)))})

(def theorem-specs [square-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-monotone theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-monotone))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
