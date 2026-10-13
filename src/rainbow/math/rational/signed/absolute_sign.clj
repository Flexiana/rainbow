(ns rainbow.math.rational.signed.absolute-sign
  "Sign characterization of absolute value over signed rationals:
     0 <= w  =>  |w| ~ w
     w <= 0  =>  |w| ~ -w
  Foundational reusable lemmas (needed by the sign case-splits in limit-product's
  distance-multiply and absolute-multiply bricks). Axiom-free; additive.

  Proof of absolute-of-nonnegative: |w| <= w from absolute-bounded-iff-deviation-rows
  (backward) given w<=w and -w<=w (the latter from 0<=w via negate-reverses-order +
  transitivity); w <= |w| is at-most-absolute; antisymmetry closes it.
  absolute-of-nonpositive reduces to the nonnegative case at -w plus absolute-negate."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute-algebra :as absolute-algebra]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.decide-order :as decide-order]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))

(defn- app [f & a] (apply function/app f a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- neg* [x] (app (function/const* 'signed/negate []) x))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- conj* [P Q] (app (function/const* 'proposition/conjunction []) P Q))
(defn- conjoin [P Q p q] (app (function/const* 'proposition/conjoin []) P Q p q))
(defn- equiv-bwd [P Q e q] (app (function/const* 'proposition/equivalence-backward []) P Q e q))
(defn- at-most-abs [x] (app (function/const* 'signed/at-most-absolute []) x))
(defn- neg-rev [a b h] (app (function/const* 'signed/negate-reverses-order []) a b h))
(def ^:private neg-zero (function/const* 'signed/negate-zero []))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-antisym [a b h1 h2] (app (function/const* 'signed/at-most-antisymmetric []) a b h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- abs-bounded-iff [v t] (app (function/const* 'signed/absolute-bounded-iff-deviation-rows []) v t))
(defn- abs-negate [x] (app (function/const* 'signed/absolute-negate []) x))
(defn- eq-refl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eq-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eq-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))

;; 0 <= w  ->  |w| ~ w
(def absolute-of-nonnegative-spec
  {:name 'signed/absolute-of-nonnegative
   :universes []
   :type (function/forall [['w signed] ['h (sle szero 'w)]] (seqv (abs* 'w) 'w))
   :value
   (function/lam [['w signed] ['h (sle szero 'w)]]
                 (let [;; -w <= 0 : negate-reverses-order 0 w h : -w <= -0 ; rewrite -0 ~ 0
                       nro (neg-rev szero 'w 'h)                       ; sle (negate w) (negate 0)
                       nw<=0 (le-resp (neg* 'w) (neg* 'w) (neg* szero) szero
                                      (eq-refl (neg* 'w)) neg-zero nro)  ; sle (negate w) 0
                       nw<=w (le-trans (neg* 'w) szero 'w nw<=0 'h)    ; sle (negate w) w
                       P (sle (abs* 'w) 'w)
                       Q (conj* (sle 'w 'w) (sle (neg* 'w) 'w))
                       abs<=w (equiv-bwd P Q (abs-bounded-iff 'w 'w)
                                         (conjoin (sle 'w 'w) (sle (neg* 'w) 'w) (le-refl 'w) nw<=w))  ; |w| <= w
                       w<=abs (at-most-abs 'w)]                          ; w <= |w|
                   (le-antisym (abs* 'w) 'w abs<=w w<=abs)))})

;; w <= 0  ->  |w| ~ -w
(def absolute-of-nonpositive-spec
  {:name 'signed/absolute-of-nonpositive
   :universes []
   :type (function/forall [['w signed] ['h (sle 'w szero)]] (seqv (abs* 'w) (neg* 'w)))
   :value
   (function/lam [['w signed] ['h (sle 'w szero)]]
                 (let [;; 0 <= -w : negate-reverses-order w 0 h : -0 <= -w ; rewrite -0 ~ 0
                       nro (neg-rev 'w szero 'h)                       ; sle (negate 0) (negate w)
                       zero<=nw (le-resp (neg* szero) szero (neg* 'w) (neg* 'w)
                                         neg-zero (eq-refl (neg* 'w)) nro)  ; sle 0 (negate w)
           ;; |(-w)| ~ (-w)  by absolute-of-nonnegative at (-w)
                       absnw-nw (app (function/const* 'signed/absolute-of-nonnegative []) (neg* 'w) zero<=nw)  ; seqv |(-w)| (-w)
           ;; |(-w)| ~ |w|  by absolute-negate
                       absnw-absw (abs-negate 'w)                       ; seqv |(-w)| |w|
           ;; |w| ~ |(-w)| ~ (-w)
                       absw-absnw (eq-sym (abs* (neg* 'w)) (abs* 'w) absnw-absw)]  ; seqv |w| |(-w)|
                   (eq-trans (abs* 'w) (abs* (neg* 'w)) (neg* 'w) absw-absnw absnw-nw)))})

(def theorem-specs [absolute-of-nonnegative-spec absolute-of-nonpositive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.absolute-algebra rainbow.math.linear.vector.dot-negate rainbow.math.rational.signed.decide-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-absolute-sign theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.absolute-sign))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
