(ns rainbow.algorithms.proofs.graph.floyd-warshall-convergence-upper
  "FLOYD-WARSHALL INVARIANT, UPPER HALF (part (U)). Tables
  D(t, i, j) over nodes < n with pivots P t < n relax at every round:

     round t :=  P t < n  /\\  forall i j < n,  D(t+1, i, j) <= D(t, i, j)
                                           /\\  D(t+1, i, j) <= D(t, i, P t) + D(t, P t, j)

  With arc weights W = D 0 and no negative closed walk, after t rounds no walk of >= 1 arc whose
  INTERMEDIATE nodes are all pivots of earlier rounds beats the entry at its ends:

     signed/fw-entries-below-walks :
       no-negative-cycles n (D 0) -> (forall s < t, round s) ->
       forall k x, 0 < k -> (forall s <= k, x s < n) ->
       (forall s, 0 < s -> s < k -> exists u < t, x s = P u) ->
       D(t, x 0, x k) <= walk-length(D 0, x, k)

  Base: no pivots means no intermediates, so the walk is one arc and D(0) is its length. Step to
  the new pivot p = P t: if no intermediate is p, every intermediate is an earlier pivot. Otherwise
  take the FIRST and LAST intermediate visits a <= b of p (nat/least-witness, nat/greatest-witness).
  The prefix 0..a and the suffix b..k avoid p as an intermediate, so the induction hypothesis
  bounds them by D(t, x 0, p) and D(t, p, x k). The middle a..b is a closed walk, so it is >= 0.
  The round's pivot bound closes it. The lengths split as in signed/walk-cut-length."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.nat.extremal-index :as extremal]
            [rainbow.algorithms.proofs.graph.floyd-warshall-convergence-attained :as attained]
            [rainbow.algorithms.proofs.graph.walk-cycle-cut :as cycle-cut]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private table-type (function/arrow nat (function/arrow nat (function/arrow nat signed))))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- nat-trans [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- falsity [] (function/const* 'proposition/falsity []))
(defn- not* [P] (function/arrow P (falsity)))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- exists-nat [pred] (proposition/existence type-level nat pred))
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))

(defn- D-at [D t i j] (app D t i j))
(defn- W0 [D] (function/lam [['u nat] ['v nat]] (app D nat-zero 'u 'v)))
(defn- arc-weights [W x] (function/lam [['t nat]] (app W (app x 't) (app x (succ 't)))))
(defn- walk-length [W x k] (expr-sum-value (arc-weights W x) k))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn- round [n D P t]
  (conj* (strict-below (app P t) n)
         (function/forall [['i nat] ['hi (strict-below 'i n)] ['j nat] ['hj (strict-below 'j n)]]
                          (conj* (sle (D-at D (succ t) 'i 'j) (D-at D t 'i 'j))
                                 (sle (D-at D (succ t) 'i 'j) (signed-add (D-at D t 'i (app P t)) (D-at D t (app P t) 'j)))))))
(defn- rounds-below [n D P t] (function/forall [['s nat] ['hs (strict-below 's t)]] (round n D P 's)))
(defn- pivot-of [P t v] (exists-nat (function/lam [['u nat]] (conj* (strict-below 'u t) (eq-nat v (app P 'u))))))
(defn- inter [P t x k]
  (function/forall [['s nat] ['hs0 (strict-below nat-zero 's)] ['hsk (strict-below 's k)]] (pivot-of P t (app x 's))))
(defn- bound-for [n D P t x k]
  (function/forall [['hk0 (strict-below nat-zero k)] ['hin (in-range n x k)] ['hint (inter P t x k)]]
                   (sle (D-at D t (app x nat-zero) (app x k)) (walk-length (W0 D) x k))))
(defn- claim [n D P t]
  (function/forall [['hr (rounds-below n D P t)] ['k nat] ['x walk-type]] (bound-for n D P t 'x 'k)))

;; round projections
(defn- round-parts [n D P t hround]
  (let [body (function/forall [['i nat] ['hi (strict-below 'i n)] ['j nat] ['hj (strict-below 'j n)]]
                              (conj* (sle (D-at D (succ t) 'i 'j) (D-at D t 'i 'j))
                                     (sle (D-at D (succ t) 'i 'j) (signed-add (D-at D t 'i (app P t)) (D-at D t (app P t) 'j)))))]
    {:pivot-below (pleft (strict-below (app P t) n) body hround)
     :mono (fn [i hi j hj] (pleft (sle (D-at D (succ t) i j) (D-at D t i j))
                                  (sle (D-at D (succ t) i j) (signed-add (D-at D t i (app P t)) (D-at D t (app P t) j)))
                                  (app (pright (strict-below (app P t) n) body hround) i hi j hj)))
     :via (fn [i hi j hj] (pright (sle (D-at D (succ t) i j) (D-at D t i j))
                                  (sle (D-at D (succ t) i j) (signed-add (D-at D t i (app P t)) (D-at D t (app P t) j)))
                                  (app (pright (strict-below (app P t) n) body hround) i hi j hj)))}))

;; Q s := 0 < s /\ s < k /\ x s = p, decidable
(defn- Q-of [x k p] (function/lam [['qs nat]] (conj* (strict-below nat-zero 'qs) (conj* (strict-below 'qs k) (eq-nat (app x 'qs) p)))))
(defn- Q-at [x k p s] (conj* (strict-below nat-zero s) (conj* (strict-below s k) (eq-nat (app x s) p))))
(defn- lt-dec
  "a < b \\/ not (a < b)"
  [a b]
  (use-disj (at-most b a) (strict-below a b) (disj* (strict-below a b) (not* (strict-below a b)))
            (app (function/const* 'nat/at-most-or-strict-below []) a b)
            (function/lam [['hba (at-most b a)]]
                          (right-disj (strict-below a b) (not* (strict-below a b))
                                      (function/lam [['hab (strict-below a b)]]
                                                    (app (function/const* 'nat/not-strictly-below-self []) a (amt (succ a) b a 'hab 'hba)))))
            (function/lam [['hab (strict-below a b)]] (left-disj (strict-below a b) (not* (strict-below a b)) 'hab))))
(defn- Q-dec [x k p]
  (function/lam
   [['ds nat]]
   (let [goal (disj* (Q-at x k p 'ds) (not* (Q-at x k p 'ds)))
         no (fn [f] (right-disj (Q-at x k p 'ds) (not* (Q-at x k p 'ds)) f))]
     (use-disj (strict-below nat-zero 'ds) (not* (strict-below nat-zero 'ds)) goal (lt-dec nat-zero 'ds)
               (function/lam
                [['h0 (strict-below nat-zero 'ds)]]
                (use-disj (strict-below 'ds k) (not* (strict-below 'ds k)) goal (lt-dec 'ds k)
                          (function/lam
                           [['hk (strict-below 'ds k)]]
                           (use-disj (eq-nat (app x 'ds) p) (not* (eq-nat (app x 'ds) p)) goal (@#'rainbow.math.nat.pigeonhole/eq-or-not (app x 'ds) p)
                                     (function/lam [['he (eq-nat (app x 'ds) p)]]
                                                   (left-disj (Q-at x k p 'ds) (not* (Q-at x k p 'ds))
                                                              (conjoin (strict-below nat-zero 'ds) (conj* (strict-below 'ds k) (eq-nat (app x 'ds) p)) 'h0
                                                                       (conjoin (strict-below 'ds k) (eq-nat (app x 'ds) p) 'hk 'he))))
                                     (function/lam [['hn (not* (eq-nat (app x 'ds) p))]]
                                                   (no (function/lam [['q (Q-at x k p 'ds)]] (app 'hn (pright (strict-below 'ds k) (eq-nat (app x 'ds) p) (pright (strict-below nat-zero 'ds) (conj* (strict-below 'ds k) (eq-nat (app x 'ds) p)) 'q))))))))
                          (function/lam [['hn (not* (strict-below 'ds k))]]
                                        (no (function/lam [['q (Q-at x k p 'ds)]] (app 'hn (pleft (strict-below 'ds k) (eq-nat (app x 'ds) p) (pright (strict-below nat-zero 'ds) (conj* (strict-below 'ds k) (eq-nat (app x 'ds) p)) 'q))))))))
               (function/lam [['hn (not* (strict-below nat-zero 'ds))]]
                             (no (function/lam [['q (Q-at x k p 'ds)]] (app 'hn (pleft (strict-below nat-zero 'ds) (conj* (strict-below 'ds k) (eq-nat (app x 'ds) p)) 'q)))))))))

(defn- q-parts [x k p s q]
  {:pos (pleft (strict-below nat-zero s) (conj* (strict-below s k) (eq-nat (app x s) p)) q)
   :below (pleft (strict-below s k) (eq-nat (app x s) p) (pright (strict-below nat-zero s) (conj* (strict-below s k) (eq-nat (app x s) p)) q))
   :hit (pright (strict-below s k) (eq-nat (app x s) p) (pright (strict-below nat-zero s) (conj* (strict-below s k) (eq-nat (app x s) p)) q))})

(defn- make-q [x k p s h0 hk he]
  (conjoin (strict-below nat-zero s) (conj* (strict-below s k) (eq-nat (app x s) p)) h0
           (conjoin (strict-below s k) (eq-nat (app x s) p) hk he)))

(defn- narrow-pivot
  "an intermediate pivot-of (t+1) that is not p = P t is a pivot-of t"
  [P t v hpv hne]
  (app hpv (pivot-of P t v)
       (function/lam
        [['u-np nat] ['pu-np (conj* (strict-below 'u-np (succ t)) (eq-nat v (app P 'u-np)))]]
        (let [hu (pleft (strict-below 'u-np (succ t)) (eq-nat v (app P 'u-np)) 'pu-np)
              he (pright (strict-below 'u-np (succ t)) (eq-nat v (app P 'u-np)) 'pu-np)]
          (use-disj (eq-nat 'u-np t) (strict-below 'u-np t) (pivot-of P t v)
                    (app (function/const* 'nat/at-most-split []) 'u-np t (@#'rainbow.math.nat.pigeonhole/le-of-below-succ 'u-np t hu))
                    (function/lam [['h-ut (eq-nat 'u-np t)]]
                                  (explode (pivot-of P t v) (app hne (nat-trans v (app P 'u-np) (app P t) he
                                                                                (subst-nat 'u-np t 'h-ut (function/lam [['z-np nat]] (eq-nat (app P 'u-np) (app P 'z-np))) (nat-refl (app P 'u-np)))))))
                    (function/lam [['h-lt (strict-below 'u-np t)]]
                                  (witness (function/lam [['u2 nat]] (conj* (strict-below 'u2 t) (eq-nat v (app P 'u2)))) 'u-np
                                           (conjoin (strict-below 'u-np t) (eq-nat v (app P 'u-np)) 'h-lt he))))))))

(def upper-spec
  {:name 'signed/fw-entries-below-walks :universes []
   :type (function/forall [['n nat] ['D table-type] ['P walk-type] ['hneg (cycle-cut/no-negative-cycles 'n (W0 'D))] ['t nat]]
                          (claim 'n 'D 'P 't))
   :value
   (function/lam
    [['n nat] ['D table-type] ['P walk-type] ['hneg (cycle-cut/no-negative-cycles 'n (W0 'D))] ['t nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['tt nat]] (claim 'n 'D 'P 'tt))
         ;; t = 0: no pivots, so the walk has one arc
         (function/lam
          [['hr (rounds-below 'n 'D 'P nat-zero)] ['k nat] ['x walk-type]
           ['hk0 (strict-below nat-zero 'k)] ['hin (in-range 'n 'x 'k)] ['hint (inter 'P nat-zero 'x 'k)]]
          (let [goal (sle (D-at 'D nat-zero (app 'x nat-zero) (app 'x 'k)) (walk-length (W0 'D) 'x 'k))
                one (succ nat-zero)]
            (use-disj (at-most (succ one) 'k) (strict-below 'k (succ one)) goal
                      (app (function/const* 'nat/at-most-or-strict-below []) 'k (succ one))
                      ;; k >= 2: position 1 is an intermediate, and there are no pivots yet
                      (function/lam [['h2 (at-most (succ one) 'k)]]
                                    (app (app 'hint one (sb-self nat-zero) 'h2) goal
                                         (function/lam [['u0 nat] ['pu0 (conj* (strict-below 'u0 nat-zero) (eq-nat (app 'x one) (app 'P 'u0)))]]
                                                       (@#'rainbow.math.nat.pigeonhole/below-zero-absurd 'u0 (pleft (strict-below 'u0 nat-zero) (eq-nat (app 'x one) (app 'P 'u0)) 'pu0) goal))))
                      ;; k < 2 and k > 0: k = 1, and D 0 is the arc's length 0 + D0(x0, x1)
                      (function/lam [['hl2 (strict-below 'k (succ one))]]
                                    (let [k-le1 (@#'rainbow.math.nat.pigeonhole/le-of-below-succ 'k one 'hl2)
                                          k1 (use-disj (eq-nat 'k one) (strict-below 'k one) (eq-nat 'k one)
                                                       (app (function/const* 'nat/at-most-split []) 'k one k-le1)
                                                       (function/lam [['he (eq-nat 'k one)]] 'he)
                                                       (function/lam [['hl (strict-below 'k one)]]
                                                                     (explode (eq-nat 'k one)
                                                                              (app (function/const* 'nat/not-strictly-below-self []) nat-zero
                                                                                   (amt one 'k nat-zero 'hk0 (@#'rainbow.math.nat.pigeonhole/le-of-below-succ 'k nat-zero 'hl))))))
                                          d (D-at 'D nat-zero (app 'x nat-zero) (app 'x one))
                                          at-one (le-respects d d d (signed-add szero d) (equiv-refl d)
                                                              (equiv-sym (signed-add szero d) d
                                                                         (equiv-trans (signed-add szero d) (signed-add d szero) d (app (function/const* 'signed/add-commutative []) szero d)
                                                                                      (app (function/const* 'signed/add-zero-right []) d)))
                                                              (app (function/const* 'signed/at-most-reflexive []) d))]
                                      (subst-nat one 'k (nat-sym 'k one k1)
                                                 (function/lam [['kq nat]] (sle (D-at 'D nat-zero (app 'x nat-zero) (app 'x 'kq)) (walk-length (W0 'D) 'x 'kq)))
                                                 at-one))))))
         (function/lam
          [['t nat] ['ih (claim 'n 'D 'P 't)] ['hr (rounds-below 'n 'D 'P (succ 't))] ['k nat] ['x walk-type]
           ['hk0 (strict-below nat-zero 'k)] ['hin (in-range 'n 'x 'k)] ['hint (inter 'P (succ 't) 'x 'k)]]
          (let [t1 (succ 't) p (app 'P 't)
                hr-now (function/lam [['s nat] ['hs (strict-below 's 't)]] (app 'hr 's (sb-weaken 's 't 'hs)))
                {:keys [pivot-below mono via]} (round-parts 'n 'D 'P 't (app 'hr 't (sb-self 't)))
                x0 (app 'x nat-zero) xk (app 'x 'k)
                x0-below (app 'hin nat-zero (witness (function/lam [['e0 nat]] (eq-nat (nadd nat-zero 'e0) 'k)) 'k (nat-refl 'k)))
                xk-below (app 'hin 'k (at-most-refl 'k))
                L (walk-length (W0 'D) 'x 'k)
                goal (sle (D-at 'D t1 x0 xk) L)
                Q (Q-of 'x 'k p) Qd (Q-dec 'x 'k p)
                P0 (function/lam [['s nat]] (conj* (at-most 's 'k) (app Q 's)))]
            (use-disj (exists-nat P0) (function/forall [['s nat] ['hs (at-most 's 'k)]] (not* (app Q 's))) goal
                      (app (function/const* 'nat/bounded-search-decidable []) Q Qd 'k)
                      ;; p is an intermediate: split at its first and last visits
                      (function/lam
                       [['hsome (exists-nat P0)]]
                       (app (app (function/const* 'nat/least-witness []) Q Qd 'k 'hsome) goal
                            (function/lam
                             [['a nat] ['pa (conj* (at-most 'a 'k) (conj* (app Q 'a) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'a)]] (not* (app Q 's2)))))]]
                             (app (app (function/const* 'nat/greatest-witness []) Q Qd 'k 'hsome) goal
                                  (function/lam
                                   [['b nat] ['pb (conj* (at-most 'b 'k) (conj* (app Q 'b) (function/forall [['s3 nat] ['hs3 (strict-below 'b 's3)] ['hk3 (at-most 's3 'k)]] (not* (app Q 's3)))))]]
                                   (let [least-rest (conj* (app Q 'a) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'a)]] (not* (app Q 's2))))
                                         qa (pleft (app Q 'a) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'a)]] (not* (app Q 's2))) (pright (at-most 'a 'k) least-rest 'pa))
                                         a-least (pright (app Q 'a) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'a)]] (not* (app Q 's2))) (pright (at-most 'a 'k) least-rest 'pa))
                                         great-rest (conj* (app Q 'b) (function/forall [['s3 nat] ['hs3 (strict-below 'b 's3)] ['hk3 (at-most 's3 'k)]] (not* (app Q 's3))))
                                         qb (pleft (app Q 'b) (function/forall [['s3 nat] ['hs3 (strict-below 'b 's3)] ['hk3 (at-most 's3 'k)]] (not* (app Q 's3))) (pright (at-most 'b 'k) great-rest 'pb))
                                         b-great (pright (app Q 'b) (function/forall [['s3 nat] ['hs3 (strict-below 'b 's3)] ['hk3 (at-most 's3 'k)]] (not* (app Q 's3))) (pright (at-most 'b 'k) great-rest 'pb))
                                         qa* (q-parts 'x 'k p 'a qa) qb* (q-parts 'x 'k p 'b qb)
                                         ;; a <= b: b < a would contradict a being least
                                         a-le-b (use-disj (at-most 'a 'b) (strict-below 'b 'a) (at-most 'a 'b)
                                                          (app (function/const* 'nat/at-most-or-strict-below []) 'b 'a)
                                                          (function/lam [['h (at-most 'a 'b)]] 'h)
                                                          (function/lam [['h (strict-below 'b 'a)]] (explode (at-most 'a 'b) (app a-least 'b 'h qb))))]
                                     ;; b = d + a, k = c + b
                                     (app a-le-b goal
                                          (function/lam
                                           [['d-ab nat] ['pd-ab (eq-nat (nadd 'a 'd-ab) 'b)]]
                                           (app (:below qb*) goal
                                                (function/lam
                                                 [['c-bk nat] ['pc-bk (eq-nat (nadd (succ 'b) 'c-bk) 'k)]]
                                                 (let [d 'd-ab c (succ 'c-bk)
                                                       b-eq (nat-trans 'b (nadd 'a d) (nadd d 'a) (nat-sym (nadd 'a d) 'b 'pd-ab) (app (function/const* 'nat/add-commutative []) 'a d))
                                                       ;; k = succ b + c' = succ (b + c') = b + succ c' = c + b
                                                       k-eq (nat-trans 'k (succ (nadd 'b 'c-bk)) (nadd c 'b)
                                                                       (nat-sym (succ (nadd 'b 'c-bk)) 'k 'pc-bk)
                                                                       (nat-trans (succ (nadd 'b 'c-bk)) (nadd 'b c) (nadd c 'b)
                                                                                  (nat-sym (nadd 'b c) (succ (nadd 'b 'c-bk)) (app (function/const* 'nat/add-successor-right []) 'b 'c-bk))
                                                                                  (app (function/const* 'nat/add-commutative []) 'b c)))
                                                       xa-p (:hit qa*) xb-p (:hit qb*)
                                                       Gx (arc-weights (W0 'D) 'x)
                                                       shifted (fn [off] (function/lam [['i-sh nat]] (app Gx (nadd 'i-sh off))))
                                                       ;; prefix walk x, a arcs, i -> p
                                                       pre-int (function/lam
                                                                [['s nat] ['hs0 (strict-below nat-zero 's)] ['hsk (strict-below 's 'a)]]
                                                                (let [s-lt-k (amt (succ 's) 'a 'k 'hsk (amt 'a 'b 'k a-le-b (amt 'b (succ 'b) 'k (at-most-succ 'b) (:below qb*))))]
                                                                  (narrow-pivot 'P 't (app 'x 's) (app 'hint 's 'hs0 s-lt-k)
                                                                                (function/lam [['he (eq-nat (app 'x 's) p)]] (app a-least 's 'hsk (make-q 'x 'k p 's 'hs0 s-lt-k 'he))))))
                                                       pre-range (function/lam [['s nat] ['hs (at-most 's 'a)]] (app 'hin 's (amt 's 'a 'k 'hs (amt 'a 'b 'k a-le-b (amt 'b (succ 'b) 'k (at-most-succ 'b) (:below qb*))))))
                                                       pre-bound (app 'ih hr-now 'a 'x (:pos qa*) pre-range pre-int)        ; D(t, x0, x a) <= len(x, a)
                                                       ;; suffix walk y = x shifted by b, c arcs, p -> x k
                                                       y (function/lam [['s-y nat]] (app 'x (nadd 's-y 'b)))
                                                       y-range (function/lam [['s nat] ['hs (at-most 's c)]]
                                                                             (app 'hin (nadd 's 'b)
                                                                                  (subst-nat (nadd c 'b) 'k (nat-sym 'k (nadd c 'b) k-eq) (function/lam [['z-k nat]] (at-most (nadd 's 'b) 'z-k))
                                                                                             (app (function/const* 'nat/add-right-monotone []) 'b 's c 'hs))))
                                                       y-int (function/lam
                                                              [['s nat] ['hs0 (strict-below nat-zero 's)] ['hsk (strict-below 's c)]]
                                                              (let [sb (nadd 's 'b)
                                                                    sb-pos (amt (succ nat-zero) (succ 'b) sb (app (function/const* 'nat/successor-monotone []) nat-zero 'b (witness (function/lam [['e0 nat]] (eq-nat (nadd nat-zero 'e0) 'b)) 'b (nat-refl 'b)))
                                                                                (app (function/const* 'nat/add-right-monotone []) 'b (succ nat-zero) 's 'hs0))
                                                                    sb-lt-k (subst-nat (nadd c 'b) 'k (nat-sym 'k (nadd c 'b) k-eq) (function/lam [['z-k nat]] (strict-below sb 'z-k))
                                                                                       (app (function/const* 'nat/add-right-monotone []) 'b (succ 's) c 'hsk))
                                                                    b-lt-sb (app (function/const* 'nat/add-right-monotone []) 'b (succ nat-zero) 's 'hs0)]
                                                                (narrow-pivot 'P 't (app 'x sb) (app 'hint sb sb-pos sb-lt-k)
                                                                              (function/lam [['he (eq-nat (app 'x sb) p)]]
                                                                                            (app b-great sb b-lt-sb (amt sb (succ sb) 'k (at-most-succ sb) sb-lt-k) (make-q 'x 'k p sb sb-pos sb-lt-k 'he))))))
                                                       suf-bound (app 'ih hr-now c y (app (function/const* 'nat/successor-monotone []) nat-zero 'c-bk (witness (function/lam [['e0 nat]] (eq-nat (nadd nat-zero 'e0) 'c-bk)) 'c-bk (nat-refl 'c-bk)))
                                                                      y-range y-int)                                                    ; D(t, x b, x (c+b)) <= len(y, c)
                                                       ;; middle: closed walk x shifted by a, d arcs
                                                       z (function/lam [['s-z nat]] (app 'x (nadd 's-z 'a)))
                                                       z-range (function/lam [['s nat] ['hs (at-most 's d)]]
                                                                             (app 'hin (nadd 's 'a)
                                                                                  (amt (nadd 's 'a) 'b 'k
                                                                                       (subst-nat (nadd d 'a) 'b (nat-sym 'b (nadd d 'a) b-eq) (function/lam [['z-b nat]] (at-most (nadd 's 'a) 'z-b))
                                                                                                  (app (function/const* 'nat/add-right-monotone []) 'a 's d 'hs))
                                                                                       (amt 'b (succ 'b) 'k (at-most-succ 'b) (:below qb*)))))
                                                       z-closed (nat-trans (app 'x (nadd d 'a)) (app 'x 'b) (app 'x 'a)
                                                                           (subst-nat (nadd d 'a) 'b (nat-sym 'b (nadd d 'a) b-eq) (function/lam [['z-b nat]] (eq-nat (app 'x (nadd d 'a)) (app 'x 'z-b))) (nat-refl (app 'x (nadd d 'a))))
                                                                           (nat-trans (app 'x 'b) p (app 'x 'a) xb-p (nat-sym (app 'x 'a) p xa-p)))
                                                       cyc-nonneg (app 'hneg z d z-range z-closed)
                                                       ;; lengths at the literal k = c + (d + a)
                                                       kk (nadd c (nadd d 'a))
                                                       A1 (app (function/const* 'signed/expr-sum-value-append []) Gx (nadd d 'a) c)   ; len(x, kk) ~ len(x, d+a) + len(y', c)
                                                       A2 (app (function/const* 'signed/expr-sum-value-append []) Gx 'a d)             ; len(x, d+a) ~ len(x, a) + len(z, d)
                                                       px (expr-sum-value Gx 'a) cy (expr-sum-value (shifted 'a) d) sx (expr-sum-value (shifted (nadd d 'a)) c)
                                                       Lkk (walk-length (W0 'D) 'x kk)
                                                       ;; len(x, kk) >= px + sx
                                                       lower (let [px-le (le-respects (signed-add px szero) px (signed-add px cy) (signed-add px cy)
                                                                                      (app (function/const* 'signed/add-zero-right []) px) (equiv-refl (signed-add px cy))
                                                                                      (app (function/const* 'signed/add-left-monotone []) szero cy px cyc-nonneg))
                                                                   step (app (function/const* 'signed/add-right-monotone []) px (signed-add px cy) sx px-le)]
                                                               (le-respects (signed-add px sx) (signed-add px sx) (signed-add (signed-add px cy) sx) Lkk
                                                                            (equiv-refl (signed-add px sx))
                                                                            (equiv-trans (signed-add (signed-add px cy) sx) (signed-add (expr-sum-value Gx (nadd d 'a)) sx) Lkk
                                                                                         (app (function/const* 'signed/add-respects-equivalence []) (signed-add px cy) (expr-sum-value Gx (nadd d 'a)) sx sx
                                                                                              (equiv-sym (expr-sum-value Gx (nadd d 'a)) (signed-add px cy) A2) (equiv-refl sx))
                                                                                         (equiv-sym Lkk (signed-add (expr-sum-value Gx (nadd d 'a)) sx) A1))
                                                                            step))
                                                       ;; D(t, x0, p) + D(t, p, x kk) <= px + sx, with the suffix read at the literal index
                                                       x-kk (app 'x kk)
                                                       suf-at-kk (subst-nat (nadd c 'b) kk
                                                                            (subst-nat 'b (nadd d 'a) b-eq (function/lam [['z-b nat]] (eq-nat (nadd c 'b) (nadd c 'z-b))) (nat-refl (nadd c 'b)))
                                                                            (function/lam [['z-k nat]] (sle (D-at 'D 't (app y nat-zero) (app 'x 'z-k)) (expr-sum-value (arc-weights (W0 'D) y) c)))
                                                                            suf-bound)
                                                       ;; y's arcs are x's shifted by b = d + a
                                                       suf-at-kk2 (subst-nat 'b (nadd d 'a) b-eq
                                                                             (function/lam [['z-b nat]] (sle (D-at 'D 't (app 'x 'z-b) x-kk) (expr-sum-value (shifted 'z-b) c)))
                                                                             suf-at-kk)
                                                       xb-kk (subst-nat (app 'x (nadd d 'a)) p
                                                                        (nat-trans (app 'x (nadd d 'a)) (app 'x 'b) p
                                                                                   (subst-nat (nadd d 'a) 'b (nat-sym 'b (nadd d 'a) b-eq) (function/lam [['z-b nat]] (eq-nat (app 'x (nadd d 'a)) (app 'x 'z-b))) (nat-refl (app 'x (nadd d 'a))))
                                                                                   xb-p)
                                                                        (function/lam [['z-p nat]] (sle (D-at 'D 't 'z-p x-kk) sx)) suf-at-kk2)
                                                       pre-p (subst-nat (app 'x 'a) p xa-p (function/lam [['z-p nat]] (sle (D-at 'D 't x0 'z-p) px)) pre-bound)
                                                       both (app (function/const* 'signed/add-monotone []) (D-at 'D 't x0 p) px (D-at 'D 't p x-kk) sx pre-p xb-kk)
                                                       kk-below (subst-nat 'k kk (nat-trans 'k (nadd c 'b) kk k-eq
                                                                                            (subst-nat 'b (nadd d 'a) b-eq (function/lam [['z-b nat]] (eq-nat (nadd c 'b) (nadd c 'z-b))) (nat-refl (nadd c 'b))))
                                                                           (function/lam [['z-k nat]] (strict-below (app 'x 'z-k) 'n)) xk-below)
                                                       at-kk (le-trans (D-at 'D t1 x0 x-kk) (signed-add (D-at 'D 't x0 p) (D-at 'D 't p x-kk)) Lkk
                                                                       (via x0 x0-below x-kk kk-below)
                                                                       (le-trans (signed-add (D-at 'D 't x0 p) (D-at 'D 't p x-kk)) (signed-add px sx) Lkk both lower))
                                                       k-kk (nat-trans 'k (nadd c 'b) kk k-eq
                                                                       (subst-nat 'b (nadd d 'a) b-eq (function/lam [['z-b nat]] (eq-nat (nadd c 'b) (nadd c 'z-b))) (nat-refl (nadd c 'b))))]
                                                   (subst-nat kk 'k (nat-sym 'k kk k-kk)
                                                              (function/lam [['z-k nat]] (sle (D-at 'D t1 x0 (app 'x 'z-k)) (walk-length (W0 'D) 'x 'z-k)))
                                                              at-kk))))))))))))
                      ;; p is not an intermediate: every intermediate is an earlier pivot
                      (function/lam
                       [['hnone (function/forall [['s nat] ['hs (at-most 's 'k)]] (not* (app Q 's)))]]
                       (let [int-t (function/lam
                                    [['s nat] ['hs0 (strict-below nat-zero 's)] ['hsk (strict-below 's 'k)]]
                                    (narrow-pivot 'P 't (app 'x 's) (app 'hint 's 'hs0 'hsk)
                                                  (function/lam [['he (eq-nat (app 'x 's) p)]]
                                                                (app 'hnone 's (amt 's (succ 's) 'k (at-most-succ 's) 'hsk) (make-q 'x 'k p 's 'hs0 'hsk 'he)))))]
                         (le-trans (D-at 'D t1 x0 xk) (D-at 'D 't x0 xk) L
                                   (mono x0 x0-below xk xk-below)
                                   (app 'ih hr-now 'k 'x 'hk0 'hin int-t)))))))
         't))})

(def theorem-specs [upper-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      attained/extend-environment
      extremal/extend-environment
      (support/extend-with :fw-convergence-upper theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
