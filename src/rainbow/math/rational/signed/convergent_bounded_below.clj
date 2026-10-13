(ns rainbow.math.rational.signed.convergent-bounded-below
  "Brick 1 of analysis/limit-reciprocal: a convergent sequence is bounded BELOW near
  its limit. Mirror of analysis/convergent-bounded.

  `analysis/convergent-bounded-below` : if s converges to L with modulus Ms, then for
  every radius r and index n at or past `Ms r`, `|L| - r <= |s n|`. Stated generally in
  r (no half-identity, no L != 0 hypothesis); the reciprocal proof instantiates r = |L|/2
  to obtain the constant lower bound |s n| >= |L|/2 that keeps the eps-scaling divisor
  fixed (not varying in n).

  Proof: read the radius-r band `close L r (s n)` off convergence; convert to
  `distance (s n) L <= r`; then the OTHER reverse triangle
  `|L| = |(L - s n) + s n| <= |L - s n| + |s n| = distance L (s n) + |s n|`,
  with `distance L (s n) ~ distance (s n) L <= r` (distance-symmetric), gives
  `|L| <= r + |s n|`, hence `|L| - r <= |s n|` (subtract-at-most-of-additive-upper).
  Axiom-free; additive; does not touch the LP checker.

  Env chain: signed-convergence, signed-additive-distance, signed-distance-triangle,
  signed-recovery-laws (as convergent-bounded), plus signed-distance (distance-symmetric)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convergence :as convergence]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]
            [rainbow.math.rational.signed.distance-triangle :as distance-triangle]
            [rainbow.math.rational.signed.recovery-laws :as recovery-laws]
            [rainbow.math.rational.signed.distance :as distance]))

(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-seq (function/arrow nat signed))
(def ^:private modulus (function/arrow signed nat))

(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist [a b] (app (function/const* 'signed/distance []) a b))
(defn- erefl [x] (app (function/const* 'signed/equivalent-reflexive []) x))
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- converges [s L M] (app (function/const* 'analysis/converges []) s L M))
(defn- nat-le [a b] (app (function/const* 'nat/at-most []) a b))
(defn- p-left [P Q h] (app (function/const* 'proposition/left []) P Q h))
(defn- p-right [P Q h] (app (function/const* 'proposition/right []) P Q h))
(defn- au-of-sub [a b c h] (app (function/const* 'signed/additive-upper-of-subtract-at-most []) a b c h))
(defn- dist-of-close [l r e h1 h2] (app (function/const* 'signed/distance-at-most-of-additive-closeness []) l r e h1 h2))
(defn- abs-tri [l r] (app (function/const* 'signed/absolute-add-triangle []) l r))
(defn- abs-resp [a b h] (app (function/const* 'signed/absolute-respects-equivalence []) a b h))
(defn- sub-then-add [a b] (app (function/const* 'signed/subtract-then-add []) a b))
(defn- add-monotone [a b c d h1 h2] (app (function/const* 'signed/add-monotone []) a b c d h1 h2))
(defn- le-refl [x] (app (function/const* 'signed/at-most-reflexive []) x))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-resp [a b c d hab hcd hord] (app (function/const* 'signed/at-most-respects-equivalence []) a b c d hab hcd hord))
(defn- dist-sym [a b] (app (function/const* 'signed/distance-symmetric []) a b))
(defn- sub-at-most [a b c h] (app (function/const* 'signed/subtract-at-most-of-additive-upper []) a b c h))

(def convergent-bounded-below-spec
  {:name 'analysis/convergent-bounded-below
   :universes []
   :type
   (function/forall
    [['s sig-seq] ['L signed] ['Ms modulus] ['conv (converges 's 'L 'Ms)]
     ['r signed] ['n nat] ['hn (nat-le (app 'Ms 'r) 'n)]]
    (sle (ssub (abs* 'L) 'r) (abs* (app 's 'n))))
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['Ms modulus] ['conv (converges 's 'L 'Ms)]
     ['r signed] ['n nat] ['hn (nat-le (app 'Ms 'r) 'n)]]
    (let [sn (app 's 'n)
          cl (app 'conv 'r 'n 'hn)                 ; close L r (s n) = conj (L-r<=s n)(s n<=L+r)
          P1 (sle (ssub 'L 'r) sn)
          P2 (sle sn (sadd 'L 'r))
          a1 (p-left P1 P2 cl)                      ; L - r <= s n
          a2 (p-right P1 P2 cl)                     ; s n <= L + r
          au (au-of-sub 'L 'r sn a1)               ; L <= r + s n
          rc (le-resp 'L 'L (sadd 'r sn) (sadd sn 'r)
                      (erefl 'L) (add-comm 'r sn) au)  ; L <= s n + r
          dc (dist-of-close sn 'L 'r a2 rc)        ; distance (s n) L <= r
          ;; reverse triangle: |L| = |(L - s n) + s n| <= |L - s n| + |s n|
          diff (ssub 'L sn)                        ; L - s n
          combo (sadd diff sn)                     ; (L - s n) + s n
          sta (sub-then-add 'L sn)                 ; combo ~ L
          tri (abs-tri diff sn)                    ; |combo| <= |L - s n| + |s n|
          rhs (sadd (abs* diff) (abs* sn))
          t1 (le-resp (abs* combo) (abs* 'L) rhs rhs
                      (abs-resp combo 'L sta) (erefl rhs) tri)  ; |L| <= |L - s n| + |s n|
          ;; |L - s n| = distance L (s n) ~ distance (s n) L <= r
          dLsn-le-r (le-resp (dist sn 'L) (dist 'L sn) 'r 'r
                             (dist-sym sn 'L) (erefl 'r) dc)     ; |L - s n| <= r  (defeq dist L sn)
          am (add-monotone (abs* diff) 'r (abs* sn) (abs* sn)
                           dLsn-le-r (le-refl (abs* sn)))        ; |L-s n| + |s n| <= r + |s n|
          t2 (le-trans (abs* 'L) rhs (sadd 'r (abs* sn)) t1 am)  ; |L| <= r + |s n|
          ]
      (sub-at-most (abs* 'L) 'r (abs* sn) t2)))})   ; |L| - r <= |s n|

(def theorem-specs [convergent-bounded-below-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convergence rainbow.math.rational.signed.additive-distance rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.recovery-laws rainbow.math.rational.signed.distance])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-convergent-bounded-below theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.convergent-bounded-below))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
