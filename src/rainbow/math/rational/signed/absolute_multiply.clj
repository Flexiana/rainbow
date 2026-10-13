(ns rainbow.math.rational.signed.absolute-multiply
  "Brick 3 of limit-product: |a * b| ~ |a| * |b| over signed rationals.

  signed/absolute-multiply : seqv (|a*b|) (|a|*|b|), by a four-way sign case-split
  (nested Bool.rec on decide-at-most 0 a and 0 b). In each quadrant the sign of a*b is
  fixed by the multiply-sign lemmas (multiply-nonnegative / -nonnegative-nonpositive /
  -nonpositive), |a*b| collapses via absolute-of-nonnegative/-nonpositive, and |a|*|b|
  is rewritten to the same normal form using absolute-of-sign + multiply-negate.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def ^:private tl [:succ [:zero]])
(def ^:private pl [:zero])
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private btrue (function/const* 'data/true []))
(def ^:private bfalse (function/const* 'data/false []))

(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- neg* [x] (app (function/const* 'signed/negate []) x))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-bool [x y] (function/equality tl bool x y))
(defn- refl-bool [x] (app (function/const* 'equality/reflexive [tl]) bool x))
(defn- eq-refl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eq-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eq-tr [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
;; mrre p q c h(p-q) : (p*c) ~ (q*c)   ; mlre p q c h(p-q) : (c*p) ~ (c*q)
(defn- mrre [p q c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) p q c h))
(defn- mlre [p q c h] (app (function/const* 'signed/multiply-left-respects-equivalence []) p q c h))
(defn- mnl [a b] (app (function/const* 'signed/multiply-negate-left []) a b))
(defn- mnr [a b] (app (function/const* 'signed/multiply-negate-right []) a b))
(defn- neg-inv [x] (app (function/const* 'signed/negate-involutive []) x))
(defn- neg-resp [a b h] (app (function/const* 'signed/negate-respects-equivalence []) a b h))
(defn- comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- nn-of-le [w h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) w h))
(defn- np-of-le [w h] (app (function/const* 'signed/nonpositive-of-at-most-zero []) w h))
(defn- le-of-nn [w h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) w h))
(defn- le-of-np [w h] (app (function/const* 'signed/at-most-zero-of-nonpositive []) w h))
(defn- mul-nn [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- mul-nnp [a b ha hb] (app (function/const* 'signed/multiply-nonnegative-nonpositive []) a b ha hb))
(defn- mul-np [a b ha hb] (app (function/const* 'signed/multiply-nonpositive []) a b ha hb))
(defn- abs-nn [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- abs-np [w h] (app (function/const* 'signed/absolute-of-nonpositive []) w h))
(defn- decide [a b] (app (function/const* 'signed/decide-at-most []) a b))
(defn- t-sound [a b h] (app (function/const* 'signed/decide-at-most-true-sound []) a b h))
(defn- f-rev [a b h] (app (function/const* 'signed/decide-at-most-false-reverse []) a b h))
(defn- bool-rec [motive fc tc t] (app (function/const* 'data/Bool.rec [pl]) motive fc tc t))

(def absolute-multiply-spec
  {:name 'signed/absolute-multiply
   :universes []
   :type (function/forall [['a signed] ['b signed]] (seqv (abs* (smul 'a 'b)) (smul (abs* 'a) (abs* 'b))))
   :value
   (function/lam [['a signed] ['b signed]]
                 (let [ab (smul 'a 'b)
                       absab (abs* ab)
                       prod (smul (abs* 'a) (abs* 'b))            ; |a|*|b|
                       goal (seqv absab prod)
           ;; |a|*|b| ~ (form a)*(form b), given absa: |a|~(form a), absb: |b|~(form b)
                       prod-to (fn [forma formb absa absb]
                                 (eq-tr prod (smul forma (abs* 'b)) (smul forma formb)
                                        (mrre (abs* 'a) forma (abs* 'b) absa)
                                        (mlre (abs* 'b) formb forma absb)))
           ;; ---- case a>=0, b>=0 : a*b>=0 ; |a*b|~a*b ; |a|*|b|~a*b
                       case-pp (fn [ha hb]
                                 (let [ab>=0 (le-of-nn ab (mul-nn 'a 'b (nn-of-le 'a ha) (nn-of-le 'b hb)))
                                       e1 (abs-nn ab ab>=0)                                   ; |a*b| ~ a*b
                                       prodAB (prod-to 'a 'b (abs-nn 'a ha) (abs-nn 'b hb))]  ; |a|*|b| ~ a*b
                                   (eq-tr absab ab prod e1 (eq-sym prod ab prodAB))))
           ;; ---- case a>=0, b<=0 : a*b<=0 ; |a*b|~ -(a*b) ; |a|*|b|~ a*(-b)~ -(a*b)
                       case-pn (fn [ha hb]
                                 (let [ab<=0 (le-of-np ab (mul-nnp 'a 'b (nn-of-le 'a ha) (np-of-le 'b hb)))
                                       e1 (abs-np ab ab<=0)                                   ; |a*b| ~ -(a*b)
                                       prodANB (prod-to 'a (neg* 'b) (abs-nn 'a ha) (abs-np 'b hb))  ; |a|*|b| ~ a*(-b)
                                       anbNAB (mnr 'a 'b)                                    ; a*(-b) ~ -(a*b)
                                       prodNAB (eq-tr prod (smul 'a (neg* 'b)) (neg* ab) prodANB anbNAB)]
                                   (eq-tr absab (neg* ab) prod e1 (eq-sym prod (neg* ab) prodNAB))))
           ;; ---- case a<=0, b>=0 : a*b<=0 ; via commute for the sign ; |a|*|b|~ (-a)*b~ -(a*b)
                       case-np (fn [ha hb]
                                 (let [ba<=0 (le-of-np (smul 'b 'a) (mul-nnp 'b 'a (nn-of-le 'b hb) (np-of-le 'a ha)))
                                       ab<=0 (le-resp (smul 'b 'a) ab szero szero
                                                      (eq-sym ab (smul 'b 'a) (comm 'a 'b)) (eq-refl szero) ba<=0)  ; a*b<=0
                                       e1 (abs-np ab ab<=0)                                   ; |a*b| ~ -(a*b)
                                       prodNABz (prod-to (neg* 'a) 'b (abs-np 'a ha) (abs-nn 'b hb))  ; |a|*|b| ~ (-a)*b
                                       nabzNAB (mnl 'a 'b)                                   ; (-a)*b ~ -(a*b)
                                       prodNAB (eq-tr prod (smul (neg* 'a) 'b) (neg* ab) prodNABz nabzNAB)]
                                   (eq-tr absab (neg* ab) prod e1 (eq-sym prod (neg* ab) prodNAB))))
           ;; ---- case a<=0, b<=0 : a*b>=0 ; |a|*|b|~ (-a)*(-b)~ a*b
                       case-nn (fn [ha hb]
                                 (let [ab>=0 (le-of-nn ab (mul-np 'a 'b (np-of-le 'a ha) (np-of-le 'b hb)))
                                       e1 (abs-nn ab ab>=0)                                   ; |a*b| ~ a*b
                                       prodNANB (prod-to (neg* 'a) (neg* 'b) (abs-np 'a ha) (abs-np 'b hb))  ; |a|*|b| ~ (-a)*(-b)
                           ;; (-a)*(-b) ~ -((-a)*b) ~ -(-(a*b)) ~ a*b
                                       s3 (mnr (neg* 'a) 'b)                                  ; (-a)*(-b) ~ -((-a)*b)
                                       s4 (neg-resp (smul (neg* 'a) 'b) (neg* ab) (mnl 'a 'b))  ; -((-a)*b) ~ -(-(a*b))
                                       s5 (neg-inv ab)                                        ; -(-(a*b)) ~ a*b
                                       nanbAB (eq-tr (smul (neg* 'a) (neg* 'b)) (neg* (smul (neg* 'a) 'b)) ab
                                                       s3 (eq-tr (neg* (smul (neg* 'a) 'b)) (neg* (neg* ab)) ab s4 s5))
                                       prodAB (eq-tr prod (smul (neg* 'a) (neg* 'b)) ab prodNANB nanbAB)]
                                   (eq-tr absab ab prod e1 (eq-sym prod ab prodAB))))
                       da (decide szero 'a)
                       db (decide szero 'b)
                       motive-a (function/lam [['ba bool]] (function/arrow (eq-bool da 'ba) goal))
                       motive-b (function/lam [['bb bool]] (function/arrow (eq-bool db 'bb) goal))
           ;; inner splits, parameterised by a's sign proof (ha)
                       inner-a>=0 (fn [ha]
                                    (app (bool-rec motive-b
                                                   (function/lam [['hbe (eq-bool db bfalse)]] (case-pn ha (f-rev szero 'b 'hbe)))
                                                   (function/lam [['hbe (eq-bool db btrue)]] (case-pp ha (t-sound szero 'b 'hbe)))
                                                   db)
                                         (refl-bool db)))
                       inner-a<=0 (fn [ha]
                                    (app (bool-rec motive-b
                                                   (function/lam [['hbe (eq-bool db bfalse)]] (case-nn ha (f-rev szero 'b 'hbe)))
                                                   (function/lam [['hbe (eq-bool db btrue)]] (case-np ha (t-sound szero 'b 'hbe)))
                                                   db)
                                         (refl-bool db)))]
                   (app (bool-rec motive-a
                                  (function/lam [['hae (eq-bool da bfalse)]] (inner-a<=0 (f-rev szero 'a 'hae)))
                                  (function/lam [['hae (eq-bool da btrue)]] (inner-a>=0 (t-sound szero 'a 'hae)))
                                  da)
                        (refl-bool da))))})

(def theorem-specs [absolute-multiply-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.absolute-sign rainbow.math.rational.signed.multiply-ring rainbow.math.linear.vector.dot-negate])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-absolute-multiply theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.absolute-multiply))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
