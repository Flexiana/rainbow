(ns rainbow.math.rational.signed.distance-product
  "Brick 4 (core) of limit-product: the bilinear distance bound for a product.

  analysis/distance-product : d(x*y, L*M) <= |x|*d(y,M) + |M|*d(x,L).
  Proof: triangle through x*M, d(x*y,x*M) <= |x|*d(y,M) by brick 2
  (distance-multiply-left-absolute at w=x), and d(x*M,L*M) <= |M|*d(x,L) by the
  right-factor variant distance-multiply-right-absolute (brick 2 + commutativity);
  add-monotone + transitivity combine. Axiom-free; additive.

  Also exports signed/distance-multiply-right-absolute : d(x*w, y*w) <= |w|*d(x,y)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-multiply-absolute :as dma]
            [rainbow.math.rational.signed.distance-triangle :as distance-triangle]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist* [a b] (app (function/const* 'signed/distance []) a b))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- eq-refl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- eq-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- comm [a b] (app (function/const* 'signed/multiply-commutative []) a b))
(defn- dist-resp [a b c d hab hcd] (app (function/const* 'signed/distance-respects-equivalence []) a b c d hab hcd))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- tri [a b c] (app (function/const* 'signed/distance-triangle []) a b c))
(defn- add-mono [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- le-tr [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- dml-abs [w x y] (app (function/const* 'analysis/distance-multiply-left-absolute []) w x y))

;; d(x*w, y*w) <= |w| * d(x,y)  -- right-factor variant of brick 2 via commutativity
(def distance-multiply-right-absolute-spec
  {:name 'signed/distance-multiply-right-absolute
   :universes []
   :type (function/forall [['x signed] ['y signed] ['w signed]]
                          (sle (dist* (smul 'x 'w) (smul 'y 'w)) (smul (abs* 'w) (dist* 'x 'y))))
   :value
   (function/lam [['x signed] ['y signed] ['w signed]]
                 (let [rhs (smul (abs* 'w) (dist* 'x 'y))
                       lw (dist* (smul 'w 'x) (smul 'w 'y))          ; d(w*x, w*y)
                       rw (dist* (smul 'x 'w) (smul 'y 'w))          ; d(x*w, y*w)
                       dresp (dist-resp (smul 'x 'w) (smul 'w 'x) (smul 'y 'w) (smul 'w 'y)
                                        (comm 'x 'w) (comm 'y 'w))    ; seqv (d(x*w,y*w)) (d(w*x,w*y))
                       base (dml-abs 'w 'x 'y)]                       ; d(w*x,w*y) <= |w|*d(x,y)
                   (le-resp lw rw rhs rhs (eq-sym rw lw dresp) (eq-refl rhs) base)))})

(defn- dmr-abs [x y w] (app (function/const* 'signed/distance-multiply-right-absolute []) x y w))

;; d(x*y, L*M) <= |x|*d(y,M) + |M|*d(x,L)
(def distance-product-spec
  {:name 'analysis/distance-product
   :universes []
   :type (function/forall [['x signed] ['y signed] ['L signed] ['M signed]]
                          (sle (dist* (smul 'x 'y) (smul 'L 'M))
                               (sadd (smul (abs* 'x) (dist* 'y 'M)) (smul (abs* 'M) (dist* 'x 'L)))))
   :value
   (function/lam [['x signed] ['y signed] ['L signed] ['M signed]]
                 (let [xy (smul 'x 'y) xM (smul 'x 'M) LM (smul 'L 'M)
                       dLeft (dist* xy xM)                            ; d(x*y, x*M)
                       dRight (dist* xM LM)                           ; d(x*M, L*M)
                       t (tri xy xM LM)                               ; d(x*y,L*M) <= dLeft + dRight
                       left (dml-abs 'x 'y 'M)                        ; dLeft <= |x|*d(y,M)
                       right (dmr-abs 'x 'L 'M)                       ; dRight <= |M|*d(x,L)
                       bnd (add-mono dLeft (smul (abs* 'x) (dist* 'y 'M)) dRight (smul (abs* 'M) (dist* 'x 'L)) left right)]
                   (le-tr (dist* xy LM) (sadd dLeft dRight)
                          (sadd (smul (abs* 'x) (dist* 'y 'M)) (smul (abs* 'M) (dist* 'x 'L)))
                          t bnd)))})

(def theorem-specs [distance-multiply-right-absolute-spec distance-product-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distance-multiply-absolute rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-distance-product theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.distance-product))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
