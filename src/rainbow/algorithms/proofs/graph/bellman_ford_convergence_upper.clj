(ns rainbow.algorithms.proofs.graph.bellman-ford-convergence-upper
  "BELLMAN-FORD CONVERGENCE, UPPER HALF (second half,
  part (U)). Label rounds L(t, v) on nodes v < n with arc weights W(u, v) relax at every round:

     round t :=  forall j < n,  L(t+1, j) <= L(t, j)  /\\  forall i < n, L(t+1, j) <= L(t, i) + W(i, j)

  (exactly the bound half of signed/bford-round-reading, so a chain of accepted Bellman-Ford round
  stores gives it). Then after r rounds no walk of at most r arcs beats the label at its end:

     signed/bford-labels-below-walks :
       forall n W L r, (forall t < r, round t) ->
       forall k x, k <= r -> (forall t <= k, x t < n) ->
       L(r, x k) <= L(0, x 0) + walk-length(x, k)

  where a walk is a node sequence x 0 .. x k and walk-length(x, k) =
  signed/expr-sum-value (fun t. W(x t, x (t+1))) k. With L(0, .) = (0, M, ..., M) this is: after
  r rounds, d_r(v) is at most the length of every walk of at most r arcs from the source.
  The other half (R), that d_r(v) is ATTAINED by such a walk, uses the attainment part of the
  reading.

  Proof by induction on r. If the walk has k <= r arcs, the previous round's bound plus
  L(r+1, .) <= L(r, .) closes it. If k = r + 1, the prefix walk of r arcs gives
  L(r, x r) <= L(0, x 0) + walk-length(x, r), and round r's arc bound at (x r, x (r+1)) adds the
  last arc. walk-length(x, r+1) is walk-length(x, r) + W(x r, x (r+1)) by definition."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.one-hot-selects :as one-hot-selects]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.rational.signed.add-associative :as add-associative]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private weight-type (function/arrow nat (function/arrow nat signed)))
(def ^:private label-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-refl [a] (app (function/const* 'signed/at-most-reflexive []) a))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))

(defn- L-at [L t v] (app L t v))
(defn- W-at [W u v] (app W u v))
(defn- walk-length [W x k] (expr-sum-value (function/lam [['t nat]] (W-at W (app x 't) (app x (succ 't)))) k))
(defn- round [n W L t]
  (function/forall [['j nat] ['hj (strict-below 'j n)]]
                   (conj* (sle (L-at L (succ t) 'j) (L-at L t 'j))
                          (function/forall [['i nat] ['hi (strict-below 'i n)]]
                                           (sle (L-at L (succ t) 'j) (signed-add (L-at L t 'i) (W-at W 'i 'j)))))))
(defn- rounds-below [n W L r] (function/forall [['t nat] ['ht (strict-below 't r)]] (round n W L 't)))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn- bound-for [n W L r x k]
  (function/arrow (in-range n x k) (sle (L-at L r (app x k)) (signed-add (L-at L nat-zero (app x nat-zero)) (walk-length W x k)))))
(defn- claim [n W L r]
  (function/forall [['hr (rounds-below n W L r)] ['k nat] ['x walk-type] ['hk (at-most 'k r)]]
                   (bound-for n W L r 'x 'k)))

(defn- monotone-part [n W L t hround j hj]
  (pleft (sle (L-at L (succ t) j) (L-at L t j))
         (function/forall [['i nat] ['hi (strict-below 'i n)]] (sle (L-at L (succ t) j) (signed-add (L-at L t 'i) (W-at W 'i j))))
         (app hround j hj)))
(defn- arc-part [n W L t hround j hj i hi]
  (app (pright (sle (L-at L (succ t) j) (L-at L t j))
               (function/forall [['i nat] ['hi (strict-below 'i n)]] (sle (L-at L (succ t) j) (signed-add (L-at L t 'i) (W-at W 'i j))))
               (app hround j hj))
       i hi))

(def labels-below-walks-spec
  {:name 'signed/bford-labels-below-walks :universes []
   :type (function/forall [['n nat] ['W weight-type] ['L label-type] ['r nat]] (claim 'n 'W 'L 'r))
   :value
   (function/lam
    [['n nat] ['W weight-type] ['L label-type] ['r nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['rr nat]] (claim 'n 'W 'L 'rr))
         ;; r = 0: k <= 0 forces k = 0, and L(0, x 0) <= L(0, x 0) + 0
         (function/lam
          [['hr (rounds-below 'n 'W 'L nat-zero)] ['k nat] ['x walk-type] ['hk (at-most 'k nat-zero)]]
          (let [goal (fn [kk] (bound-for 'n 'W 'L nat-zero 'x kk))
                L0 (L-at 'L nat-zero (app 'x nat-zero))
                at-zero (function/lam [['hin (in-range 'n 'x nat-zero)]]
                                      (le-respects L0 L0 L0 (signed-add L0 szero) (equiv-refl L0)
                                                   (equiv-sym (signed-add L0 szero) L0 (app (function/const* 'signed/add-zero-right []) L0))
                                                   (le-refl L0)))]
            (use-disj (eq-nat 'k nat-zero) (strict-below 'k nat-zero) (goal 'k)
                      (app (function/const* 'nat/at-most-split []) 'k nat-zero 'hk)
                      (function/lam [['he (eq-nat 'k nat-zero)]]
                                    (subst-nat nat-zero 'k (nat-sym 'k nat-zero 'he) (function/lam [['kk nat]] (goal 'kk)) at-zero))
                      (function/lam [['hl (strict-below 'k nat-zero)]]
                                    (app 'hl (goal 'k)
                                         (function/lam [['e nat] ['pf (eq-nat (nadd (succ 'k) 'e) nat-zero)]]
                                                       (explode (goal 'k) (app (function/const* 'nat/zero-not-successor []) (nadd 'k 'e)
                                                                               (nat-sym (succ (nadd 'k 'e)) nat-zero 'pf)))))))))
         (function/lam
          [['r nat] ['ih (claim 'n 'W 'L 'r)]
           ['hr (rounds-below 'n 'W 'L (succ 'r))] ['k nat] ['x walk-type] ['hk (at-most 'k (succ 'r))]]
          (let [r1 (succ 'r)
                hr-now (function/lam [['t nat] ['ht (strict-below 't 'r)]] (app 'hr 't (sb-weaken 't 'r 'ht)))
                round-r (app 'hr 'r (sb-self 'r))
                goal (fn [kk] (bound-for 'n 'W 'L r1 'x kk))
                L0 (L-at 'L nat-zero (app 'x nat-zero))
                ;; k <= r: the previous round's bound, then L(r+1, .) <= L(r, .)
                shorter
                (function/lam
                 [['hle (strict-below 'k r1)] ['hin (in-range 'n 'x 'k)]]
                 (let [k-le-r (app 'hle (at-most 'k 'r)
                                   (function/lam [['e nat] ['pf (eq-nat (nadd (succ 'k) 'e) r1)]]
                                                 (app (function/const* 'proposition/witness [type-level]) nat
                                                      (function/lam [['e2 nat]] (eq-nat (nadd 'k 'e2) 'r)) 'e
                                                      (app (function/const* 'nat/successor-injective []) (nadd 'k 'e) 'r 'pf))))
                       before (app 'ih hr-now 'k 'x k-le-r 'hin)
                       xk (app 'x 'k)
                       xk-below (app 'hin 'k (at-most-refl 'k))]
                   (le-trans (L-at 'L r1 xk) (L-at 'L 'r xk) (signed-add L0 (walk-length 'W 'x 'k))
                             (monotone-part 'n 'W 'L 'r round-r xk xk-below) before)))
                ;; k = r + 1: prefix of r arcs, then round r's arc bound on the last arc
                full
                (function/lam
                 [['hin (in-range 'n 'x r1)]]
                 (let [hin-r (function/lam [['t nat] ['ht (at-most 't 'r)]] (app 'hin 't (amt 't 'r r1 'ht (at-most-succ 'r))))
                       prefix (app 'ih hr-now 'r 'x (at-most-refl 'r) hin-r)          ; L(r, x r) <= L0 + len r
                       xr (app 'x 'r) xr1 (app 'x r1)
                       xr-below (app 'hin 'r (at-most-succ 'r))
                       xr1-below (app 'hin r1 (at-most-refl r1))
                       w (W-at 'W xr xr1) len (walk-length 'W 'x 'r)
                       arc (arc-part 'n 'W 'L 'r round-r xr1 xr1-below xr xr-below)   ; L(r+1, x r1) <= L(r, x r) + w
                       lifted (app (function/const* 'signed/add-right-monotone []) (L-at 'L 'r xr) (signed-add L0 len) w prefix)
                       chain (le-trans (L-at 'L r1 xr1) (signed-add (L-at 'L 'r xr) w) (signed-add (signed-add L0 len) w) arc lifted)]
                   (le-respects (L-at 'L r1 xr1) (L-at 'L r1 xr1) (signed-add (signed-add L0 len) w) (signed-add L0 (signed-add len w))
                                (equiv-refl (L-at 'L r1 xr1)) (app (function/const* 'signed/add-associative []) L0 len w) chain)))]
            (use-disj (eq-nat 'k r1) (strict-below 'k r1) (goal 'k)
                      (app (function/const* 'nat/at-most-split []) 'k r1 'hk)
                      (function/lam [['he (eq-nat 'k r1)]]
                                    (subst-nat r1 'k (nat-sym 'k r1 'he) (function/lam [['kk nat]] (goal 'kk)) full))
                      (function/lam [['hl (strict-below 'k r1)]]
                                    (function/lam [['hin (in-range 'n 'x 'k)]] (app shorter 'hl 'hin))))))
         'r))})

(def theorem-specs [labels-below-walks-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.one-hot-selects rainbow.math.nat.divmod rainbow.math.rational.signed.add-associative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :bford-convergence-upper theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.graph.bellman-ford-convergence-upper))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
