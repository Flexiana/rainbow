(ns rainbow.algorithms.proofs.graph.walk-shorten
  "CYCLE REMOVAL: without negative closed walks, every walk
  over n nodes can be replaced by one of FEWER THAN n arcs with the same ends that is no longer:

     signed/walk-shorten :
       no-negative-cycles n W -> forall k x, (forall t <= k, x t < n) ->
       exists k', k' < n /\\ exists y, (forall t <= k', y t < n) /\\ y 0 = x 0 /\\ y k' = x k
                              /\\ walk-length (y, k') <= walk-length (x, k)

  Proof by strong induction on a length bound K. A walk of fewer than n arcs is kept. A walk of
  k >= n arcs visits x 0 .. x n, n + 1 nodes below n, so nat/pigeonhole gives a < b <= n with
  x a = x b. With b = (e + 1) + a and k = c + b, signed/walk-cut-length cuts the cycle. The cut
  walk has c + a < k arcs, the same ends and no greater length, and the induction hypothesis
  finishes it. This is what makes n - 1 Bellman-Ford rounds enough."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.algorithms.proofs.graph.walk-cycle-cut :as cycle-cut]
            [rainbow.math.nat.pigeonhole :as pigeonhole]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private weight-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
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
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- witness [carrier P w pf] (app (function/const* 'proposition/witness [type-level]) carrier P w pf))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-refl [a] (app (function/const* 'signed/at-most-reflexive []) a))

(defn- walk-length [W x k] (@#'cycle-cut/walk-length W x k))
(defn- in-range [n x k] (@#'cycle-cut/in-range n x k))
(defn- cut [x a d] (@#'cycle-cut/cut x a d))
(defn- cut-at [x a d t] (@#'cycle-cut/cut-at x a d t))

(defn- short-walk-body [n W x k]
  (function/lam [['k2 nat]]
                (conj* (strict-below 'k2 n)
                       (proposition/existence type-level walk-type
                                              (function/lam [['y walk-type]]
                                                            (conj* (in-range n 'y 'k2)
                                                                   (conj* (eq-nat (app 'y nat-zero) (app x nat-zero))
                                                                          (conj* (eq-nat (app 'y 'k2) (app x k))
                                                                                 (sle (walk-length W 'y 'k2) (walk-length W x k))))))))))
(defn- shortened [n W x k] (proposition/existence type-level nat (short-walk-body n W x k)))
(defn- claim [n W K]
  (function/forall [['k nat] ['hk (at-most 'k K)] ['x walk-type] ['hin (in-range n 'x 'k)]] (shortened n W 'x 'k)))

(defn- keep-walk
  "k < n: the walk itself"
  [n W x k hkn hin]
  (let [body (short-walk-body n W x k)
        y-body (function/lam [['y walk-type]]
                             (conj* (in-range n 'y k) (conj* (eq-nat (app 'y nat-zero) (app x nat-zero))
                                                             (conj* (eq-nat (app 'y k) (app x k)) (sle (walk-length W 'y k) (walk-length W x k))))))]
    (witness nat body k
             (conjoin (strict-below k n) (proposition/existence type-level walk-type y-body) hkn
                      (witness walk-type y-body x
                               (conjoin (in-range n x k) (conj* (eq-nat (app x nat-zero) (app x nat-zero)) (conj* (eq-nat (app x k) (app x k)) (sle (walk-length W x k) (walk-length W x k))))
                                        hin
                                        (conjoin (eq-nat (app x nat-zero) (app x nat-zero)) (conj* (eq-nat (app x k) (app x k)) (sle (walk-length W x k) (walk-length W x k)))
                                                 (nat-refl (app x nat-zero))
                                                 (conjoin (eq-nat (app x k) (app x k)) (sle (walk-length W x k) (walk-length W x k))
                                                          (nat-refl (app x k)) (le-refl (walk-length W x k))))))))))

(defn- compose
  "a shortened walk of the cut walk z (which has z 0 = x 0, z kz = x k, len z <= len x) is a
   shortened walk of x"
  [n W x k z kz z0 zk zlen hz-short]
  (app hz-short (shortened n W x k)
       (function/lam
        [['k2 nat] ['p (app (short-walk-body n W z kz) 'k2)]]
        (let [y-body-z (function/lam [['y walk-type]]
                                     (conj* (in-range n 'y 'k2) (conj* (eq-nat (app 'y nat-zero) (app z nat-zero))
                                                                       (conj* (eq-nat (app 'y 'k2) (app z kz)) (sle (walk-length W 'y 'k2) (walk-length W z kz))))))
              y-body-x (function/lam [['y walk-type]]
                                     (conj* (in-range n 'y 'k2) (conj* (eq-nat (app 'y nat-zero) (app x nat-zero))
                                                                       (conj* (eq-nat (app 'y 'k2) (app x k)) (sle (walk-length W 'y 'k2) (walk-length W x k))))))
              hk2 (pleft (strict-below 'k2 n) (proposition/existence type-level walk-type y-body-z) 'p)
              ex (pright (strict-below 'k2 n) (proposition/existence type-level walk-type y-body-z) 'p)]
          (app ex (shortened n W x k)
               (function/lam
                [['y walk-type] ['py (app y-body-z 'y)]]
                (let [r1 (conj* (eq-nat (app 'y nat-zero) (app z nat-zero)) (conj* (eq-nat (app 'y 'k2) (app z kz)) (sle (walk-length W 'y 'k2) (walk-length W z kz))))
                      r2 (conj* (eq-nat (app 'y 'k2) (app z kz)) (sle (walk-length W 'y 'k2) (walk-length W z kz)))
                      yin (pleft (in-range n 'y 'k2) r1 'py)
                      y0 (pleft (eq-nat (app 'y nat-zero) (app z nat-zero)) r2 (pright (in-range n 'y 'k2) r1 'py))
                      yk (pleft (eq-nat (app 'y 'k2) (app z kz)) (sle (walk-length W 'y 'k2) (walk-length W z kz)) (pright (eq-nat (app 'y nat-zero) (app z nat-zero)) r2 (pright (in-range n 'y 'k2) r1 'py)))
                      ylen (pright (eq-nat (app 'y 'k2) (app z kz)) (sle (walk-length W 'y 'k2) (walk-length W z kz)) (pright (eq-nat (app 'y nat-zero) (app z nat-zero)) r2 (pright (in-range n 'y 'k2) r1 'py)))]
                  (witness nat (short-walk-body n W x k) 'k2
                           (conjoin (strict-below 'k2 n) (proposition/existence type-level walk-type y-body-x) hk2
                                    (witness walk-type y-body-x 'y
                                             (conjoin (in-range n 'y 'k2) (conj* (eq-nat (app 'y nat-zero) (app x nat-zero)) (conj* (eq-nat (app 'y 'k2) (app x k)) (sle (walk-length W 'y 'k2) (walk-length W x k))))
                                                      yin
                                                      (conjoin (eq-nat (app 'y nat-zero) (app x nat-zero)) (conj* (eq-nat (app 'y 'k2) (app x k)) (sle (walk-length W 'y 'k2) (walk-length W x k)))
                                                               (nat-trans (app 'y nat-zero) (app z nat-zero) (app x nat-zero) y0 z0)
                                                               (conjoin (eq-nat (app 'y 'k2) (app x k)) (sle (walk-length W 'y 'k2) (walk-length W x k))
                                                                        (nat-trans (app 'y 'k2) (app z kz) (app x k) yk zk)
                                                                        (le-trans (walk-length W 'y 'k2) (walk-length W z kz) (walk-length W x k) ylen zlen))))))))))))))

(def shorten-spec
  {:name 'signed/walk-shorten-bounded :universes []
   :type (function/forall [['n nat] ['W weight-type] ['hneg (cycle-cut/no-negative-cycles 'n 'W)] ['K nat]] (claim 'n 'W 'K))
   :value
   (function/lam
    [['n nat] ['W weight-type] ['hneg (cycle-cut/no-negative-cycles 'n 'W)] ['K nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['KK nat]] (claim 'n 'W 'KK))
         ;; K = 0: k = 0 < n (x 0 < n)
         (function/lam
          [['k nat] ['hk (at-most 'k nat-zero)] ['x walk-type] ['hin (in-range 'n 'x 'k)]]
          (let [k0 (@#'pigeonhole/zero-of-le-zero 'k 'hk)
                x0 (app 'x nat-zero)
                zero-below (app (app 'hin 'k (at-most-refl 'k)) (strict-below nat-zero 'n)
                                (function/lam [['e nat] ['pf (eq-nat (nadd (succ (app 'x 'k)) 'e) 'n)]]
                                              (witness nat (function/lam [['e2 nat]] (eq-nat (nadd (succ nat-zero) 'e2) 'n)) (nadd (app 'x 'k) 'e) 'pf)))
                k-below (subst-nat nat-zero 'k (nat-sym 'k nat-zero k0) (function/lam [['z nat]] (strict-below 'z 'n)) zero-below)]
            (keep-walk 'n 'W 'x 'k k-below 'hin)))
         (function/lam
          [['K nat] ['ih (claim 'n 'W 'K)] ['k nat] ['hk (at-most 'k (succ 'K))] ['x walk-type] ['hin (in-range 'n 'x 'k)]]
          (let [K1 (succ 'K) goal (shortened 'n 'W 'x 'k)]
            (use-disj (eq-nat 'k K1) (strict-below 'k K1) goal
                      (app (function/const* 'nat/at-most-split []) 'k K1 'hk)
                      ;; k = K + 1
                      (function/lam
                       [['hkK (eq-nat 'k K1)]]
                       (use-disj (at-most 'n 'k) (strict-below 'k 'n) goal
                                 (app (function/const* 'nat/at-most-or-strict-below []) 'k 'n)
                                 ;; k >= n: pigeonhole, cut, recurse
                                 (function/lam
                                  [['hnk (at-most 'n 'k)]]
                                  (let [x-into (function/lam [['t nat] ['ht (at-most 't 'n)]] (app 'hin 't (amt 't 'n 'k 'ht 'hnk)))
                                        rep (app (function/const* 'nat/pigeonhole []) 'n 'x x-into)
                                        Pa (function/lam [['a nat]] (proposition/existence type-level nat (function/lam [['b nat]] (conj* (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b)))))))]
                                    (app rep goal
                                         (function/lam
                                          [['a nat] ['pa (app Pa 'a)]]
                                          (app 'pa goal
                                               (function/lam
                                                [['b nat] ['pb (conj* (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b))))]]
                                                (let [hab (pleft (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b))) 'pb)
                                                      hbn (pleft (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b)) (pright (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b))) 'pb))
                                                      hxab (pright (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b)) (pright (strict-below 'a 'b) (conj* (at-most 'b 'n) (eq-nat (app 'x 'a) (app 'x 'b))) 'pb))
                                                      hbk (amt 'b 'n 'k hbn 'hnk)]
                                                  ;; b = succ a + e = (succ e) + a ; k = b + c = c + b
                                                  (app hab goal
                                                       (function/lam
                                                        [['e nat] ['pe (eq-nat (nadd (succ 'a) 'e) 'b)]]
                                                        (app hbk goal
                                                             (function/lam
                                                              [['c nat] ['pc (eq-nat (nadd 'b 'c) 'k)]]
                                                              (let [d (succ 'e) da (nadd d 'a)
                                                                    b-da (nat-trans 'b (succ (nadd 'a 'e)) da (nat-sym (succ (nadd 'a 'e)) 'b 'pe)
                                                                                    (subst-nat (nadd 'a 'e) (nadd 'e 'a) (app (function/const* 'nat/add-commutative []) 'a 'e)
                                                                                               (function/lam [['z nat]] (eq-nat (succ (nadd 'a 'e)) (succ 'z))) (nat-refl (succ (nadd 'a 'e)))))
                                                                    k-eq (nat-trans 'k (nadd 'b 'c) (nadd 'c da) (nat-sym (nadd 'b 'c) 'k 'pc)
                                                                                    (nat-trans (nadd 'b 'c) (nadd 'c 'b) (nadd 'c da) (app (function/const* 'nat/add-commutative []) 'b 'c)
                                                                                               (subst-nat 'b da b-da (function/lam [['z nat]] (eq-nat (nadd 'c 'b) (nadd 'c 'z))) (nat-refl (nadd 'c 'b)))))
                                                                    kk (nadd 'c da)
                                                                    ;; the goal at the literal length c + (d + a), transported back to k
                                                                    at-kk
                                                                    (fn [hin-kk]
                                                                      (let [hrep (nat-trans (app 'x da) (app 'x 'b) (app 'x 'a)
                                                                                            (subst-nat 'b da b-da (function/lam [['z nat]] (eq-nat (app 'x 'z) (app 'x 'b))) (nat-refl (app 'x 'b)))
                                                                                            (nat-sym (app 'x 'a) (app 'x 'b) hxab))
                                                                            z (cut 'x 'a d) kz (nadd 'c 'a)
                                                                            z-range (app (function/const* 'nat/walk-cut-range []) 'n 'x 'a d 'c hin-kk hrep)
                                                                            z-len (app (function/const* 'signed/walk-cut-length []) 'n 'W 'hneg 'x 'a d 'c hin-kk hrep)
                                                                            z0 (app (function/const* 'nat/walk-cut-below []) 'x 'a d nat-zero
                                                                                    (witness nat (function/lam [['e2 nat]] (eq-nat (nadd nat-zero 'e2) 'a)) 'a (nat-refl 'a)))
                                                                            zk (nat-trans (cut-at 'x 'a d kz) (app 'x (nadd kz d)) (app 'x kk)
                                                                                          (app (function/const* 'nat/walk-cut-shifted []) 'x 'a d hrep kz (app (function/const* 'nat/at-most-add-left []) 'a 'c))
                                                                                          (subst-nat (nadd kz d) kk (app (function/const* 'nat/walk-shift-arith []) 'c 'a d)
                                                                                                     (function/lam [['z2 nat]] (eq-nat (app 'x (nadd kz d)) (app 'x 'z2))) (nat-refl (app 'x (nadd kz d)))))
                                                                            ;; c + a <= K: succ (c + a) <= c + succ (e + a) = k = K + 1
                                                                            kz-le (app (function/const* 'nat/at-most-successor-cancel-local []) kz 'K
                                                                                       (subst-nat 'k K1 'hkK (function/lam [['z2 nat]] (at-most (succ kz) 'z2))
                                                                                                  (subst-nat kk 'k (nat-sym 'k kk k-eq) (function/lam [['z2 nat]] (at-most (succ kz) 'z2))
                                                                                                             (app (function/const* 'nat/walk-cut-shorter []) 'c 'a 'e))))
                                                                            z-short (app 'ih kz kz-le z z-range)]
                                                                        (compose 'n 'W 'x kk z kz z0 zk z-len z-short)))]
                                                                (subst-nat kk 'k (nat-sym 'k kk k-eq) (function/lam [['z2 nat]] (shortened 'n 'W 'x 'z2))
                                                                           (at-kk (subst-nat 'k kk k-eq (function/lam [['z2 nat]] (in-range 'n 'x 'z2)) 'hin)))))))))))))))
                                 ;; k < n: keep
                                 (function/lam [['hkn (strict-below 'k 'n)]] (keep-walk 'n 'W 'x 'k 'hkn 'hin))))
                      ;; k <= K: the induction hypothesis
                      (function/lam [['hl (strict-below 'k K1)]]
                                    (app 'ih 'k (app (function/const* 'nat/at-most-successor-cancel-local []) 'k 'K 'hl) 'x 'hin)))))
         'K))})

;; succ a <= succ b |- a <= b  (a local copy of the successor cancellation, from successor-injective)
(def successor-cancel-spec
  {:name 'nat/at-most-successor-cancel-local :universes []
   :type (function/forall [['a nat] ['b nat] ['h (at-most (succ 'a) (succ 'b))]] (at-most 'a 'b))
   :value (function/lam
           [['a nat] ['b nat] ['h (at-most (succ 'a) (succ 'b))]]
           (app 'h (at-most 'a 'b)
                (function/lam [['e nat] ['pf (eq-nat (nadd (succ 'a) 'e) (succ 'b))]]
                              (witness nat (function/lam [['e2 nat]] (eq-nat (nadd 'a 'e2) 'b)) 'e
                                       (app (function/const* 'nat/successor-injective []) (nadd 'a 'e) 'b 'pf)))))})

;; succ (c + a) <= c + (succ e + a): the cut walk is strictly shorter
(def shorter-spec
  {:name 'nat/walk-cut-shorter :universes []
   :type (function/forall [['c nat] ['a nat] ['e nat]] (at-most (succ (nadd 'c 'a)) (nadd 'c (nadd (succ 'e) 'a))))
   :value (function/lam
           [['c nat] ['a nat] ['e nat]]
           (let [target (nadd 'c (succ (nadd 'e 'a)))
                 ;; c + succ (e + a) = succ (c + (e + a))
                 succ-right (app (function/const* 'nat/add-successor-right []) 'c (nadd 'e 'a))
                 ;; c + a <= c + (e + a)
                 inner (app (function/const* 'nat/add-left-monotone []) 'c 'a (nadd 'e 'a) (app (function/const* 'nat/at-most-add-left []) 'a 'e))]
             (subst-nat (succ (nadd 'c (nadd 'e 'a))) target (nat-sym target (succ (nadd 'c (nadd 'e 'a))) succ-right)
                        (function/lam [['z nat]] (at-most (succ (nadd 'c 'a)) 'z))
                        (app (function/const* 'nat/successor-monotone []) (nadd 'c 'a) (nadd 'c (nadd 'e 'a)) inner))))})

(def final-spec
  {:name 'signed/walk-shorten :universes []
   :type (function/forall [['n nat] ['W weight-type] ['hneg (cycle-cut/no-negative-cycles 'n 'W)] ['k nat] ['x walk-type] ['hin (in-range 'n 'x 'k)]]
                          (shortened 'n 'W 'x 'k))
   :value (function/lam
           [['n nat] ['W weight-type] ['hneg (cycle-cut/no-negative-cycles 'n 'W)] ['k nat] ['x walk-type] ['hin (in-range 'n 'x 'k)]]
           (app (function/const* 'signed/walk-shorten-bounded []) 'n 'W 'hneg 'k 'k (at-most-refl 'k) 'x 'hin))})

(def theorem-specs [successor-cancel-spec shorter-spec shorten-spec final-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      cycle-cut/extend-environment
      pigeonhole/extend-environment
      (support/extend-with :walk-shorten theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
