(ns rainbow.math.rational.signed.convergent-bounded
  "Brick 1 of analysis/limit-product: a convergent sequence is bounded.

  `analysis/convergent-bounded` : if s converges to L with modulus Ms, then for every
  index n at or past `Ms 1`, `|s n| <= 1 + |L|`. This is the load-bearing prerequisite
  the product proof needs (to bound the varying factor s_n) and is independently the
  first real 'convergent => bounded' fact over signed sequences (the prior
  analysis/bounded-above was nnrat-only and unconnected to converges).

  Proof: read the radius-1 band `close L 1 (s n)` off convergence; convert it to
  `distance (s n) L <= 1` (distance-at-most-of-additive-closeness, after rearranging
  the lower band L-1<=s n into L<=s n+1); then the reverse triangle
  `|s n| = |(s n - L) + L| <= |s n - L| + |L| = distance (s n) L + |L| <= 1 + |L|`
  via absolute-add-triangle + subtract-then-add + add-monotone. Axiom-free; additive;
  does not touch the LP checker.

  Env chain: signed-convergence (converges/close), signed-additive-distance (the
  distance<->band bridges), signed-distance-triangle (absolute + triangle + order
  laws), signed-recovery-laws (subtract-then-add)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.convergence :as convergence]
            [rainbow.math.rational.signed.additive-distance :as additive-distance]
            [rainbow.math.rational.signed.distance-triangle :as distance-triangle]
            [rainbow.math.rational.signed.recovery-laws :as recovery-laws]))

(def ^:private nat (function/const* 'data/Nat []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private sig-seq (function/arrow nat signed))
(def ^:private modulus (function/arrow signed nat))
(def ^:private one (function/const* 'signed/one []))

(defn- app [f & a] (apply function/app f a))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- ssub [a b] (app (function/const* 'signed/subtract []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- abs* [x] (app (function/const* 'signed/absolute []) x))
(defn- dist [a b] (app (function/const* 'signed/distance []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
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

(def convergent-bounded-spec
  {:name 'analysis/convergent-bounded
   :universes []
   :type (function/forall
          [['s sig-seq] ['L signed] ['Ms modulus] ['conv (converges 's 'L 'Ms)]
           ['n nat] ['hn (nat-le (app 'Ms one) 'n)]]
          (sle (abs* (app 's 'n)) (sadd one (abs* 'L))))
   :value
   (function/lam
    [['s sig-seq] ['L signed] ['Ms modulus] ['conv (converges 's 'L 'Ms)]
     ['n nat] ['hn (nat-le (app 'Ms one) 'n)]]
    (let [sn (app 's 'n)
          P1 (sle (ssub 'L one) sn)               ; L - 1 <= s n
          P2 (sle sn (sadd 'L one))               ; s n <= L + 1
          cl (app 'conv one 'n 'hn)               ; close L 1 (s n) = conjunction P1 P2
          a1 (p-left P1 P2 cl)                     ; L - 1 <= s n
          a2 (p-right P1 P2 cl)                    ; s n <= L + 1
          au (au-of-sub 'L one sn a1)             ; L <= 1 + s n           (add one (s n))
          ;; rearrange 1 + s n  ~  s n + 1  to feed the distance lemma's right band
          rc (le-resp 'L 'L (sadd one sn) (sadd sn one)
                      (erefl 'L) (add-comm one sn) au)  ; L <= s n + 1     (add (s n) one)
          dc (dist-of-close sn 'L one a2 rc)      ; distance (s n) L <= 1  = |s n - L| <= 1
          ;; reverse triangle: |s n| = |(s n - L) + L| <= |s n - L| + |L|
          combo (sadd (ssub sn 'L) 'L)            ; (s n - L) + L
          sta (sub-then-add sn 'L)                ; combo ~ s n
          tri (abs-tri (ssub sn 'L) 'L)           ; |combo| <= |s n - L| + |L|
          rhs (sadd (abs* (ssub sn 'L)) (abs* 'L))
          t1 (le-resp (abs* combo) (abs* sn) rhs rhs
                      (abs-resp combo sn sta) (erefl rhs) tri)  ; |s n| <= |s n - L| + |L|
          ;; |s n - L| = distance (s n) L <= 1  (defeq), and |L| <= |L|
          am (add-monotone (abs* (ssub sn 'L)) one (abs* 'L) (abs* 'L)
                           dc (le-refl (abs* 'L)))  ; |s n - L| + |L| <= 1 + |L|
          bound (sadd one (abs* 'L))]
      (le-trans (abs* sn) rhs bound t1 am)))})

(def theorem-specs [convergent-bounded-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.convergence rainbow.math.rational.signed.additive-distance rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.recovery-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-convergent-bounded theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.convergent-bounded))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
