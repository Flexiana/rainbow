(ns rainbow.math.rational.signed.close-of-distance
  "B6f lever: build a closeness band from a distance bound (the converse of dist-of-close).

    analysis/close-of-distance-at-most : distance x L <= eps -> close L eps x

  close L eps x = (L - eps <= x) AND (x <= L + eps). From |x-L| <= eps:
    x - L <= |x-L| <= eps         (at-most-absolute)      -> x <= L + eps
    L - x ~ -(x-L) <= |x-L| <= eps (negate-at-most-absolute + negate-subtract) -> L - eps <= x
  assembled with proposition/conjoin. The limit-reciprocal assembly proves
  distance (reciprocal (s n)) (reciprocal L) <= eps and lands the goal
  close (reciprocal L) eps (reciprocal (s n)) via this bridge. Axiom-free; additive; does
  not touch the LP checker."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.absolute :as absolute]
            [rainbow.math.rational.signed.distance :as distance]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]
            [rainbow.math.rational.signed.convergence :as convergence]
            [rainbow.math.rational.signed.order-transitivity :as order-transitivity]
            [rainbow.math.rational.signed.order-respects :as order-respects]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sneg [a] (app (function/const* 'signed/negate []) a))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist [a b] (app (function/const* 'signed/distance []) a b))
(defn- close* [L eps x] (app (function/const* 'analysis/close []) L eps x))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- at-most-abs [v] (app (function/const* 'signed/at-most-absolute []) v))
(defn- neg-at-most-abs [v] (app (function/const* 'signed/negate-at-most-absolute []) v))
(defn- neg-sub [a b] (app (function/const* 'signed/negate-subtract []) a b))
(defn- au-of-sub [a b c h] (app (function/const* 'signed/additive-upper-of-subtract-at-most []) a b c h))
(defn- sub-at-most [a b c h] (app (function/const* 'signed/subtract-at-most-of-additive-upper []) a b c h))
(defn- conjoin [P Q p q] (app (function/const* 'proposition/conjoin []) P Q p q))

(def close-of-distance-at-most-spec
  {:name 'analysis/close-of-distance-at-most
   :universes []
   :type (function/forall
          [['L signed] ['eps signed] ['x signed] ['hd (sle (dist 'x 'L) 'eps)]]
          (close* 'L 'eps 'x))
   :value
   (function/lam
    [['L signed] ['eps signed] ['x signed] ['hd (sle (dist 'x 'L) 'eps)]]
    (let [d (ssub 'x 'L)                                  ; x - L ; dist x L = abs d (defeq)
          ;; P2 : x <= L + eps
          xmL<=eps (le-trans d (abs* d) 'eps (at-most-abs d) 'hd)          ; x - L <= eps
          p2 (au-of-sub 'x 'L 'eps xmL<=eps)                               ; x <= L + eps
          ;; P1 : L - eps <= x
          Lmx<=abs (le-resp (sneg d) (ssub 'L 'x) (abs* d) (abs* d)
                            (neg-sub 'x 'L) (erefl (abs* d)) (neg-at-most-abs d))  ; L - x <= abs d
          Lmx<=eps (le-trans (ssub 'L 'x) (abs* d) 'eps Lmx<=abs 'hd)      ; L - x <= eps
          L<=x+eps (au-of-sub 'L 'x 'eps Lmx<=eps)                         ; L <= x + eps
          L<=eps+x (le-resp 'L 'L (sadd 'x 'eps) (sadd 'eps 'x)
                            (erefl 'L) (add-comm 'x 'eps) L<=x+eps)        ; L <= eps + x
          p1 (sub-at-most 'L 'eps 'x L<=eps+x)]                            ; L - eps <= x
      (conjoin (sle (ssub 'L 'eps) 'x) (sle 'x (sadd 'L 'eps)) p1 p2)))})

(def theorem-specs [close-of-distance-at-most-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      absolute/extend-environment
      distance/extend-environment
      additive-distance/extend-environment
      convergence/extend-environment
      order-transitivity/extend-environment
      order-respects/extend-environment
      (support/extend-with :signed-close-of-distance theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
