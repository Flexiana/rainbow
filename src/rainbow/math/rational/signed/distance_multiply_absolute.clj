(ns rainbow.math.rational.signed.distance-multiply-absolute
  "Brick 2 of limit-product: distance scales by the ABSOLUTE value of a sign-indefinite
  left factor.

  analysis/distance-multiply-left-absolute :
     d(w*x, w*y) <= |w| * d(x, y)   for ARBITRARY signed w.

  The existing signed/distance-multiply-left-nonnegative only covers 0<=w (giving
  w*d(x,y)); this lifts it to any w via a sign case-split on decide-at-most 0 w:
    - 0<=w  : the nonnegative base, then |w|~w (absolute-of-nonnegative) rewrites w to |w|.
    - w<=0  : apply the base at -w (>=0), and transport
              d((-w)*x,(-w)*y) ~ d(w*x,w*y) [multiply-negate-left + distance-negate-both]
              while |w|~-w (absolute-of-nonpositive) rewrites (-w) to |w|.
  Axiom-free; additive; does not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute-sign :as absolute-sign]
            [rainbow.math.rational.signed.distance-negate :as distance-negate]
            [rainbow.math.rational.signed.distance-multiply-nonnegative :as distance-multiply]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

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
(defn- dist* [a b] (app (function/const* 'signed/distance []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-bool [x y] (function/equality tl bool x y))
(defn- refl-bool [x] (app (function/const* 'equality/reflexive [tl]) bool x))
(defn- eq-refl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eq-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- eq-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- mrre [a b c h] (app (function/const* 'signed/multiply-right-respects-equivalence []) a b c h))
(defn- neg-rev [a b h] (app (function/const* 'signed/negate-reverses-order []) a b h))
(def ^:private neg-zero (function/const* 'signed/negate-zero []))
(defn- dmn [w x y h] (app (function/const* 'signed/distance-multiply-left-nonnegative []) w x y h))
(defn- abs-nonneg [w h] (app (function/const* 'signed/absolute-of-nonnegative []) w h))
(defn- abs-nonpos [w h] (app (function/const* 'signed/absolute-of-nonpositive []) w h))
(defn- mul-neg-left [a b] (app (function/const* 'signed/multiply-negate-left []) a b))
(defn- dist-resp [a b c d hab hcd] (app (function/const* 'signed/distance-respects-equivalence []) a b c d hab hcd))
(defn- dist-neg-both [a b] (app (function/const* 'signed/distance-negate-both []) a b))
(defn- decide [a b] (app (function/const* 'signed/decide-at-most []) a b))
(defn- true-sound [a b h] (app (function/const* 'signed/decide-at-most-true-sound []) a b h))
(defn- false-reverse [a b h] (app (function/const* 'signed/decide-at-most-false-reverse []) a b h))
(defn- bool-rec [motive fc tc t] (app (function/const* 'data/Bool.rec [pl]) motive fc tc t))

(def distance-multiply-left-absolute-spec
  {:name 'analysis/distance-multiply-left-absolute
   :universes []
   :type (function/forall [['w signed] ['x signed] ['y signed]]
                          (sle (dist* (smul 'w 'x) (smul 'w 'y)) (smul (abs* 'w) (dist* 'x 'y))))
   :value
   (function/lam [['w signed] ['x signed] ['y signed]]
                 (let [dxy (dist* 'x 'y)
                       lhs (dist* (smul 'w 'x) (smul 'w 'y))
                       goal (sle lhs (smul (abs* 'w) dxy))
                       d0w (decide szero 'w)
                       motive (function/lam [['b bool]] (function/arrow (eq-bool d0w 'b) goal))
           ;; 0 <= w
                       true-case
                       (function/lam [['ht (eq-bool d0w btrue)]]
                                     (let [h0w (true-sound szero 'w 'ht)                       ; 0 <= w
                                           base (dmn 'w 'x 'y h0w)                             ; d(w x)(w y) <= w * dxy
                                           absw-w (abs-nonneg 'w h0w)                          ; |w| ~ w
                                           w-absw (eq-sym (abs* 'w) 'w absw-w)                 ; w ~ |w|
                                           c-resp (mrre 'w (abs* 'w) dxy w-absw)]              ; w*dxy ~ |w|*dxy
                                       (le-resp lhs lhs (smul 'w dxy) (smul (abs* 'w) dxy)
                                                (eq-refl lhs) c-resp base)))
           ;; w <= 0
                       false-case
                       (function/lam [['hf (eq-bool d0w bfalse)]]
                                     (let [hw0 (false-reverse szero 'w 'hf)                    ; w <= 0
                                           nro (neg-rev 'w szero hw0)                          ; -0 <= -w
                                           zero<=nw (le-resp (neg* szero) szero (neg* 'w) (neg* 'w)
                                                             neg-zero (eq-refl (neg* 'w)) nro) ; 0 <= -w
                                           base (dmn (neg* 'w) 'x 'y zero<=nw)                 ; d((-w)x)((-w)y) <= (-w)*dxy
                                           nwx (mul-neg-left 'w 'x)                            ; (-w)*x ~ -(w*x)
                                           nwy (mul-neg-left 'w 'y)                            ; (-w)*y ~ -(w*y)
                                           dresp (dist-resp (smul (neg* 'w) 'x) (neg* (smul 'w 'x))
                                                            (smul (neg* 'w) 'y) (neg* (smul 'w 'y)) nwx nwy) ; d((-w)x,(-w)y) ~ d(-(wx),-(wy))
                                           dnb (dist-neg-both (smul 'w 'x) (smul 'w 'y))       ; d(-(wx),-(wy)) ~ d(wx,wy)
                                           dchain (eq-trans (dist* (smul (neg* 'w) 'x) (smul (neg* 'w) 'y))
                                                            (dist* (neg* (smul 'w 'x)) (neg* (smul 'w 'y)))
                                                            lhs dresp dnb)                      ; d((-w)x,(-w)y) ~ d(wx,wy)
                                           absw-nw (abs-nonpos 'w hw0)                          ; |w| ~ -w
                                           nw-absw (eq-sym (abs* 'w) (neg* 'w) absw-nw)         ; -w ~ |w|
                                           c-resp (mrre (neg* 'w) (abs* 'w) dxy nw-absw)]       ; (-w)*dxy ~ |w|*dxy
                                       (le-resp (dist* (smul (neg* 'w) 'x) (smul (neg* 'w) 'y)) lhs
                                                (smul (neg* 'w) dxy) (smul (abs* 'w) dxy)
                                                dchain c-resp base)))]
                   (app (bool-rec motive false-case true-case d0w) (refl-bool d0w))))})

(def theorem-specs [distance-multiply-left-absolute-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      absolute-sign/extend-environment
      distance-negate/extend-environment
      distance-multiply/extend-environment
      multiply-ring/extend-environment
      (support/extend-with :signed-distance-multiply-absolute theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
