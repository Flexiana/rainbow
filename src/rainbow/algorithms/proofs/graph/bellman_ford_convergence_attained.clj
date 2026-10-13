(ns rainbow.algorithms.proofs.graph.bellman-ford-convergence-attained
  "BELLMAN-FORD CONVERGENCE, ATTAINMENT HALF (second half,
  part (R)). If every round's new label is ATTAINED, i.e. equal to the old label or to some
  L(t, i) + W(i, j) (the attainment half of signed/bford-round-reading), then every label after r
  rounds is the start label of some node plus the length of a walk of at most r arcs from it:

     signed/bford-labels-attained :
       forall n W L r, (forall t < r, attained t) ->
       forall v < n, exists k, k <= r /\\
         exists x, (forall t <= k, x t < n) /\\ x k = v /\\ L(r, v) ~ L(0, x 0) + walk-length(x, k)

  With (U) (signed/bford-labels-below-walks) this is the exact r-round semantics:
     d_r(v) = min over walks x of at most r arcs ending at v of  d_0(x 0) + walk-length(x, k).

  Proof by induction on r. A kept label reuses the previous round's walk. A label attained through
  the arc (i, v) extends i's walk by v: ext x k v = fun t. if t <= k then x t else v (by
  nat/decide-at-most). The extended walk agrees with x below k + 1, so its first k arcs have the
  same length (signed/expr-sum-value-congruence-below), and its last arc is W(i, v)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.algorithms.proofs.graph.bellman-ford-convergence-upper :as upper]
            [rainbow.math.rational.signed.decide-completeness :as decide-completeness]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private weight-type (function/arrow nat (function/arrow nat signed)))
(def ^:private label-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- eq-bool [a b] (app (function/const* 'equality/Eq [type-level]) bool a b))
(defn- eq-signed [a b] (app (function/const* 'equality/Eq [type-level]) signed a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- subst-bool [x y h P px] (app (function/const* 'equality/substitution [type-level]) bool x y h P px))
(defn- subst-signed [x y h P px] (app (function/const* 'equality/substitution [type-level]) signed x y h P px))
(defn- bool-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) bool a b h))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- witness [carrier P w pf] (app (function/const* 'proposition/witness [type-level]) carrier P w pf))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- add-respects [a ah b bh e1 e2] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh e1 e2))
(defn- decide [a b] (app (function/const* 'nat/decide-at-most []) a b))

(defn- L-at [L t v] (app L t v))
(defn- W-at [W u v] (app W u v))
(defn- arc-weights [W x] (function/lam [['t nat]] (W-at W (app x 't) (app x (succ 't)))))
(defn- walk-length [W x k] (expr-sum-value (arc-weights W x) k))
(defn- ext [x k v] (function/lam [['t nat]] (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) v (app x 't) (decide 't k))))

(defn- attained-round [n W L t]
  (function/forall [['j nat] ['hj (strict-below 'j n)]]
                   (disj* (sequiv (L-at L (succ t) 'j) (L-at L t 'j))
                          (proposition/existence type-level nat
                                                 (function/lam [['i nat]] (conj* (strict-below 'i n) (sequiv (L-at L (succ t) 'j) (signed-add (L-at L t 'i) (W-at W 'i 'j)))))))))
(defn- attained-below [n W L r] (function/forall [['t nat] ['ht (strict-below 't r)]] (attained-round n W L 't)))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn- realised-by [n W L r v k]
  (proposition/existence type-level walk-type
                         (function/lam [['x walk-type]]
                                       (conj* (in-range n 'x k)
                                              (conj* (eq-nat (app 'x k) v)
                                                     (sequiv (L-at L r v) (signed-add (L-at L nat-zero (app 'x nat-zero)) (walk-length W 'x k))))))))
(defn- realised [n W L r v]
  (proposition/existence type-level nat (function/lam [['k nat]] (conj* (at-most 'k r) (realised-by n W L r v 'k)))))
(defn- claim [n W L r]
  (function/forall [['ha (attained-below n W L r)] ['v nat] ['hv (strict-below 'v n)]] (realised n W L r 'v)))

(defn- ext-below
  "t <= k |- ext x k v t = x t"
  [x k v t ht]
  (subst-bool true-value (decide t k) (bool-sym (decide t k) true-value (app (function/const* 'nat/decide-at-most-true-complete []) t k ht))
              (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) v (app x t) 'b) (app x t)))
              (nat-refl (app x t))))
(defn- ext-last
  "ext x k v (k + 1) = v"
  [x k v]
  (let [not-le (function/lam [['h (at-most (succ k) k)]] (app (function/const* 'nat/not-strictly-below-self []) k 'h))]
    (subst-bool false-value (decide (succ k) k)
                (bool-sym (decide (succ k) k) false-value (app (function/const* 'nat/decide-at-most-false-complete []) (succ k) k not-le))
                (function/lam [['b bool]] (eq-nat (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) v (app x (succ k)) 'b) v))
                (nat-refl v))))
(defn- le-of-below-succ
  "t < k + 1 |- t <= k"
  [t k h]
  (app h (at-most t k)
       (function/lam [['e nat] ['pf (eq-nat (nadd (succ t) 'e) (succ k))]]
                     (witness nat (function/lam [['e2 nat]] (eq-nat (nadd t 'e2) k)) 'e
                              (app (function/const* 'nat/successor-injective []) (nadd t 'e) k 'pf)))))
(defn- equiv-of-eq [a b h] (subst-signed a b h (function/lam [['y signed]] (sequiv a 'y)) (equiv-refl a)))

(def labels-attained-spec
  {:name 'signed/bford-labels-attained :universes []
   :type (function/forall [['n nat] ['W weight-type] ['L label-type] ['r nat]] (claim 'n 'W 'L 'r))
   :value
   (function/lam
    [['n nat] ['W weight-type] ['L label-type] ['r nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['rr nat]] (claim 'n 'W 'L 'rr))
         ;; r = 0: the empty walk at v, L(0, v) ~ L(0, v) + 0
         (function/lam
          [['ha (attained-below 'n 'W 'L nat-zero)] ['v nat] ['hv (strict-below 'v 'n)]]
          (let [x (function/lam [['t nat]] 'v) L0v (L-at 'L nat-zero 'v)
                P-walk (function/lam [['x2 walk-type]]
                                     (conj* (in-range 'n 'x2 nat-zero)
                                            (conj* (eq-nat (app 'x2 nat-zero) 'v)
                                                   (sequiv L0v (signed-add (L-at 'L nat-zero (app 'x2 nat-zero)) (walk-length 'W 'x2 nat-zero))))))
                body (conjoin (in-range 'n x nat-zero)
                              (conj* (eq-nat 'v 'v) (sequiv L0v (signed-add L0v szero)))
                              (function/lam [['t nat] ['ht (at-most 't nat-zero)]] 'hv)
                              (conjoin (eq-nat 'v 'v) (sequiv L0v (signed-add L0v szero)) (nat-refl 'v)
                                       (equiv-sym (signed-add L0v szero) L0v (app (function/const* 'signed/add-zero-right []) L0v))))]
            (witness nat (function/lam [['k nat]] (conj* (at-most 'k nat-zero) (realised-by 'n 'W 'L nat-zero 'v 'k))) nat-zero
                     (conjoin (at-most nat-zero nat-zero) (realised-by 'n 'W 'L nat-zero 'v nat-zero) (at-most-refl nat-zero)
                              (witness walk-type P-walk x body)))))
         (function/lam
          [['r nat] ['ih (claim 'n 'W 'L 'r)]
           ['ha (attained-below 'n 'W 'L (succ 'r))] ['v nat] ['hv (strict-below 'v 'n)]]
          (let [r1 (succ 'r)
                ha-now (function/lam [['t nat] ['ht (strict-below 't 'r)]] (app 'ha 't (sb-weaken 't 'r 'ht)))
                goal (realised 'n 'W 'L r1 'v)
                Lnew (L-at 'L r1 'v)
                K (fn [bound] (function/lam [['k nat]] (conj* (at-most 'k bound) (realised-by 'n 'W 'L bound 'v 'k))))
                ;; kept label: reuse the previous walk
                on-keep
                (function/lam
                 [['hk (sequiv Lnew (L-at 'L 'r 'v))]]
                 (app (app 'ih ha-now 'v 'hv) goal
                      (function/lam
                       [['k nat] ['pk (conj* (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'v 'k))]]
                       (let [k-le (pleft (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'v 'k) 'pk)
                             walk (pright (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'v 'k) 'pk)
                             Pw (fn [bound] (function/lam [['x walk-type]]
                                                          (conj* (in-range 'n 'x 'k)
                                                                 (conj* (eq-nat (app 'x 'k) 'v)
                                                                        (sequiv (L-at 'L bound 'v) (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k)))))))]
                         (witness nat (K r1) 'k
                                  (conjoin (at-most 'k r1) (realised-by 'n 'W 'L r1 'v 'k) (amt 'k 'r r1 k-le (at-most-succ 'r))
                                           (app walk (realised-by 'n 'W 'L r1 'v 'k)
                                                (function/lam
                                                 [['x walk-type] ['px (app (Pw 'r) 'x)]]
                                                 (let [rest (conj* (eq-nat (app 'x 'k) 'v) (sequiv (L-at 'L 'r 'v) (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k))))
                                                       inr (pleft (in-range 'n 'x 'k) rest 'px)
                                                       endv (pleft (eq-nat (app 'x 'k) 'v) (sequiv (L-at 'L 'r 'v) (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k))) (pright (in-range 'n 'x 'k) rest 'px))
                                                       val (pright (eq-nat (app 'x 'k) 'v) (sequiv (L-at 'L 'r 'v) (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k))) (pright (in-range 'n 'x 'k) rest 'px))
                                                       target (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k))]
                                                   (witness walk-type (Pw r1) 'x
                                                            (conjoin (in-range 'n 'x 'k) (conj* (eq-nat (app 'x 'k) 'v) (sequiv Lnew target)) inr
                                                                     (conjoin (eq-nat (app 'x 'k) 'v) (sequiv Lnew target) endv
                                                                              (equiv-trans Lnew (L-at 'L 'r 'v) target 'hk val)))))))))))))
                ;; attained through the arc (i, v): extend i's walk by v
                on-arc
                (function/lam
                 [['hx (proposition/existence type-level nat
                                              (function/lam [['i nat]] (conj* (strict-below 'i 'n) (sequiv Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v))))))]]
                 (app 'hx goal
                      (function/lam
                       [['i nat] ['pi (conj* (strict-below 'i 'n) (sequiv Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v))))]]
                       (let [hi (pleft (strict-below 'i 'n) (sequiv Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v))) 'pi)
                             via (pright (strict-below 'i 'n) (sequiv Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v))) 'pi)
                             Ki (function/lam [['k nat]] (conj* (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'i 'k)))]
                         (app (app 'ih ha-now 'i hi) goal
                              (function/lam
                               [['k nat] ['pk (app Ki 'k)]]
                               (let [k-le (pleft (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'i 'k) 'pk)
                                     walk (pright (at-most 'k 'r) (realised-by 'n 'W 'L 'r 'i 'k) 'pk)
                                     k1 (succ 'k)
                                     Pi (function/lam [['x walk-type]]
                                                      (conj* (in-range 'n 'x 'k)
                                                             (conj* (eq-nat (app 'x 'k) 'i)
                                                                    (sequiv (L-at 'L 'r 'i) (signed-add (L-at 'L nat-zero (app 'x nat-zero)) (walk-length 'W 'x 'k))))))]
                                 (app walk goal
                                      (function/lam
                                       [['x walk-type] ['px (app Pi 'x)]]
                                       (let [start (L-at 'L nat-zero (app 'x nat-zero))
                                             rest (conj* (eq-nat (app 'x 'k) 'i) (sequiv (L-at 'L 'r 'i) (signed-add start (walk-length 'W 'x 'k))))
                                             inr (pleft (in-range 'n 'x 'k) rest 'px)
                                             endi (pleft (eq-nat (app 'x 'k) 'i) (sequiv (L-at 'L 'r 'i) (signed-add start (walk-length 'W 'x 'k))) (pright (in-range 'n 'x 'k) rest 'px))
                                             val (pright (eq-nat (app 'x 'k) 'i) (sequiv (L-at 'L 'r 'i) (signed-add start (walk-length 'W 'x 'k))) (pright (in-range 'n 'x 'k) rest 'px))
                                             y (ext 'x 'k 'v)
                                             ;; y agrees with x at every t <= k
                                             y0 (ext-below 'x 'k 'v nat-zero
                                                           (witness nat (function/lam [['e nat]] (eq-nat (nadd nat-zero 'e) 'k)) 'k (nat-refl 'k)))
                                             yk (ext-below 'x 'k 'v 'k (at-most-refl 'k))
                                             ylast (ext-last 'x 'k 'v)
                                             ;; first k arcs of y have the same weights as x's
                                             agree (function/lam
                                                    [['a nat] ['ha2 (strict-below 'a 'k)]]
                                                    (let [a-le (amt 'a (succ 'a) 'k (at-most-succ 'a) 'ha2)
                                                          e1 (ext-below 'x 'k 'v 'a a-le)
                                                          e2 (ext-below 'x 'k 'v (succ 'a) 'ha2)
                                                          lhs (W-at 'W (app y 'a) (app y (succ 'a)))
                                                          s1 (subst-nat (app y 'a) (app 'x 'a) e1
                                                                        (function/lam [['z nat]] (eq-signed lhs (W-at 'W 'z (app y (succ 'a)))))
                                                                        (app (function/const* 'equality/reflexive [type-level]) signed lhs))]
                                                      (subst-nat (app y (succ 'a)) (app 'x (succ 'a)) e2
                                                                 (function/lam [['z nat]] (eq-signed lhs (W-at 'W (app 'x 'a) 'z))) s1)))
                                             same-len (equiv-of-eq (walk-length 'W y 'k) (walk-length 'W 'x 'k)
                                                                   (app (function/const* 'signed/expr-sum-value-congruence-below []) (arc-weights 'W y) (arc-weights 'W 'x) 'k agree))
                                             ;; last arc of y is W(i, v)
                                             last-w (W-at 'W (app y 'k) (app y k1))
                                             last-eq (let [s1 (subst-nat (app y 'k) 'i
                                                                         (app (function/const* 'equality/transitive [type-level]) nat (app y 'k) (app 'x 'k) 'i yk endi)
                                                                         (function/lam [['z nat]] (sequiv last-w (W-at 'W 'z (app y k1))))
                                                                         (equiv-refl last-w))]
                                                       (subst-nat (app y k1) 'v ylast (function/lam [['z nat]] (sequiv last-w (W-at 'W 'i 'z))) s1))
                                             ystart (L-at 'L nat-zero (app y nat-zero))
                                             start-eq (subst-nat (app y nat-zero) (app 'x nat-zero) y0
                                                                 (function/lam [['z nat]] (sequiv ystart (L-at 'L nat-zero 'z))) (equiv-refl ystart))
                                             ;; Lnew ~ L(r,i) + W(i,v) ~ (start + len_k x) + W(i,v) ~ start + (len_k y + last) = ystart + len_{k+1} y
                                             target (signed-add ystart (walk-length 'W y k1))
                                             step1 (add-respects (L-at 'L 'r 'i) (signed-add start (walk-length 'W 'x 'k)) (W-at 'W 'i 'v) (W-at 'W 'i 'v) val (equiv-refl (W-at 'W 'i 'v)))
                                             assoc (app (function/const* 'signed/add-associative []) start (walk-length 'W 'x 'k) (W-at 'W 'i 'v))
                                             back (add-respects start ystart (signed-add (walk-length 'W 'x 'k) (W-at 'W 'i 'v)) (walk-length 'W y k1)
                                                                (equiv-sym ystart start start-eq)
                                                                (add-respects (walk-length 'W 'x 'k) (walk-length 'W y 'k) (W-at 'W 'i 'v) last-w
                                                                              (equiv-sym (walk-length 'W y 'k) (walk-length 'W 'x 'k) same-len)
                                                                              (equiv-sym last-w (W-at 'W 'i 'v) last-eq)))
                                             value (equiv-trans Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v)) target via
                                                                (equiv-trans (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v)) (signed-add (signed-add start (walk-length 'W 'x 'k)) (W-at 'W 'i 'v)) target step1
                                                                             (equiv-trans (signed-add (signed-add start (walk-length 'W 'x 'k)) (W-at 'W 'i 'v))
                                                                                          (signed-add start (signed-add (walk-length 'W 'x 'k) (W-at 'W 'i 'v))) target assoc back)))
                                             ;; y stays in range for t <= k + 1
                                             y-range (function/lam
                                                      [['t nat] ['ht (at-most 't k1)]]
                                                      (use-disj (eq-nat 't k1) (strict-below 't k1) (strict-below (app y 't) 'n)
                                                                (app (function/const* 'nat/at-most-split []) 't k1 'ht)
                                                                (function/lam [['he (eq-nat 't k1)]]
                                                                              (subst-nat k1 't (nat-sym 't k1 'he) (function/lam [['z nat]] (strict-below (app y 'z) 'n))
                                                                                         (subst-nat 'v (app y k1) (nat-sym (app y k1) 'v ylast) (function/lam [['z nat]] (strict-below 'z 'n)) 'hv)))
                                                                (function/lam [['hl (strict-below 't k1)]]
                                                                              (let [t-le (le-of-below-succ 't 'k 'hl)]
                                                                                (subst-nat (app 'x 't) (app y 't) (nat-sym (app y 't) (app 'x 't) (ext-below 'x 'k 'v 't t-le))
                                                                                           (function/lam [['z nat]] (strict-below 'z 'n)) (app inr 't t-le))))))
                                             Pw (function/lam [['x2 walk-type]]
                                                              (conj* (in-range 'n 'x2 k1)
                                                                     (conj* (eq-nat (app 'x2 k1) 'v)
                                                                            (sequiv Lnew (signed-add (L-at 'L nat-zero (app 'x2 nat-zero)) (walk-length 'W 'x2 k1))))))]
                                         (witness nat (K r1) k1
                                                  (conjoin (at-most k1 r1) (realised-by 'n 'W 'L r1 'v k1)
                                                           (app (function/const* 'nat/successor-monotone []) 'k 'r k-le)
                                                           (witness walk-type Pw y
                                                                    (conjoin (in-range 'n y k1) (conj* (eq-nat (app y k1) 'v) (sequiv Lnew target)) y-range
                                                                             (conjoin (eq-nat (app y k1) 'v) (sequiv Lnew target) ylast value)))))))))))))))]
            (use-disj (sequiv Lnew (L-at 'L 'r 'v))
                      (proposition/existence type-level nat
                                             (function/lam [['i nat]] (conj* (strict-below 'i 'n) (sequiv Lnew (signed-add (L-at 'L 'r 'i) (W-at 'W 'i 'v))))))
                      goal (app 'ha 'r (sb-self 'r) 'v 'hv) on-keep on-arc)))
         'r))})

(def theorem-specs [labels-attained-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.graph.bellman-ford-convergence-upper rainbow.math.rational.signed.decide-completeness])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :bford-convergence-attained theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.graph.bellman-ford-convergence-attained))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
