(ns rainbow.algorithms.proofs.graph.floyd-warshall-convergence-attained
  "FLOYD-WARSHALL, ATTAINMENT HALF (second half, part (R)).
  Tables D(t, i, j) on nodes < n with pivots P(t) < n, where every round's entries are ATTAINED
  (kept, or through the pivot: the attainment part of signed/fwround-reading):

     round t :=  forall i j < n,  D(t+1, i, j) ~ D(t, i, j)  \\/  D(t+1, i, j) ~ D(t, i, P t) + D(t, P t, j)

  Then every entry after r rounds is the length of an actual walk, measured with the initial table
  as arc weights:

     signed/fw-entries-attained :
       (forall t < r, P t < n /\\ round t) -> forall i j < n,
       exists k x, (forall t <= k, x t < n) /\\ x 0 = i /\\ x k = j /\\ D(r, i, j) ~ walk-length(D 0, x, k)

  Base: the one-arc walk i, j. A kept entry keeps its walk. A pivot entry concatenates the walks
  i -> p and p -> j (signed/walk-concat), and the lengths add."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.algorithms.proofs.graph.walk-concat :as walk-concat]
            [rainbow.algorithms.proofs.graph.walk-shorten :as walk-shorten]
            [rainbow.math.nat.pigeonhole :as pigeonhole]))

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
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- nat-trans [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
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

(defn- D-at [D t i j] (app D t i j))
(defn- W0 [D] (function/lam [['u nat] ['v nat]] (app D nat-zero 'u 'v)))
(defn- walk-length [W x k] (expr-sum-value (function/lam [['t nat]] (app W (app x 't) (app x (succ 't)))) k))
(defn- in-range [n x k] (function/forall [['t nat] ['ht (at-most 't k)]] (strict-below (app x 't) n)))
(defn- pivot-round [n D P t]
  (conj* (strict-below (app P t) n)
         (function/forall [['i nat] ['hi (strict-below 'i n)] ['j nat] ['hj (strict-below 'j n)]]
                          (disj* (sequiv (D-at D (succ t) 'i 'j) (D-at D t 'i 'j))
                                 (sequiv (D-at D (succ t) 'i 'j) (signed-add (D-at D t 'i (app P t)) (D-at D t (app P t) 'j)))))))
(defn- rounds-below [n D P r] (function/forall [['t nat] ['ht (strict-below 't r)]] (pivot-round n D P 't)))
(defn- walk-body [n D r i j k]
  (function/lam [['x walk-type]]
                (conj* (in-range n 'x k)
                       (conj* (eq-nat (app 'x nat-zero) i)
                              (conj* (eq-nat (app 'x k) j)
                                     (sequiv (D-at D r i j) (walk-length (W0 D) 'x k)))))))
(defn- realised [n D r i j]
  (proposition/existence type-level nat
                         (function/lam [['k nat]] (proposition/existence type-level walk-type (walk-body n D r i j 'k)))))
(defn- claim [n D P r]
  (function/forall [['hr (rounds-below n D P r)] ['i nat] ['hi (strict-below 'i n)] ['j nat] ['hj (strict-below 'j n)]]
                   (realised n D r 'i 'j)))

(defn- pack
  "exists k x with the four facts"
  [n D r i j k x hin h0 hk hv]
  (witness nat (function/lam [['k2 nat]] (proposition/existence type-level walk-type (walk-body n D r i j 'k2))) k
           (witness walk-type (walk-body n D r i j k) x
                    (conjoin (in-range n x k) (conj* (eq-nat (app x nat-zero) i) (conj* (eq-nat (app x k) j) (sequiv (D-at D r i j) (walk-length (W0 D) x k))))
                             hin
                             (conjoin (eq-nat (app x nat-zero) i) (conj* (eq-nat (app x k) j) (sequiv (D-at D r i j) (walk-length (W0 D) x k)))
                                      h0 (conjoin (eq-nat (app x k) j) (sequiv (D-at D r i j) (walk-length (W0 D) x k)) hk hv))))))

(defn- sym [base tag] (symbol (str base "-" tag)))

(defn- unpack
  "use (realised n D r i j): (cont k x hin h0 hk hv). `tag` names the binders: nested unpacks
   must use distinct tags, or the inner binder captures the outer walk."
  [n D r i j h goal tag cont]
  (app h goal
       (function/lam
        [[(sym "kk" tag) nat] [(sym "hx" tag) (proposition/existence type-level walk-type (walk-body n D r i j (sym "kk" tag)))]]
        (app (sym "hx" tag) goal
             (function/lam
              [[(sym "xx" tag) walk-type] [(sym "px" tag) (app (walk-body n D r i j (sym "kk" tag)) (sym "xx" tag))]]
              (let [r1 (conj* (eq-nat (app (sym "xx" tag) nat-zero) i) (conj* (eq-nat (app (sym "xx" tag) (sym "kk" tag)) j) (sequiv (D-at D r i j) (walk-length (W0 D) (sym "xx" tag) (sym "kk" tag)))))
                    r2 (conj* (eq-nat (app (sym "xx" tag) (sym "kk" tag)) j) (sequiv (D-at D r i j) (walk-length (W0 D) (sym "xx" tag) (sym "kk" tag))))
                    hin (pleft (in-range n (sym "xx" tag) (sym "kk" tag)) r1 (sym "px" tag))
                    h0 (pleft (eq-nat (app (sym "xx" tag) nat-zero) i) r2 (pright (in-range n (sym "xx" tag) (sym "kk" tag)) r1 (sym "px" tag)))
                    hk (pleft (eq-nat (app (sym "xx" tag) (sym "kk" tag)) j) (sequiv (D-at D r i j) (walk-length (W0 D) (sym "xx" tag) (sym "kk" tag))) (pright (eq-nat (app (sym "xx" tag) nat-zero) i) r2 (pright (in-range n (sym "xx" tag) (sym "kk" tag)) r1 (sym "px" tag))))
                    hv (pright (eq-nat (app (sym "xx" tag) (sym "kk" tag)) j) (sequiv (D-at D r i j) (walk-length (W0 D) (sym "xx" tag) (sym "kk" tag))) (pright (eq-nat (app (sym "xx" tag) nat-zero) i) r2 (pright (in-range n (sym "xx" tag) (sym "kk" tag)) r1 (sym "px" tag))))]
                (cont (sym "kk" tag) (sym "xx" tag) hin h0 hk hv)))))))

(def attained-spec
  {:name 'signed/fw-entries-attained :universes []
   :type (function/forall [['n nat] ['D table-type] ['P walk-type] ['r nat]] (claim 'n 'D 'P 'r))
   :value
   (function/lam
    [['n nat] ['D table-type] ['P walk-type] ['r nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['rr nat]] (claim 'n 'D 'P 'rr))
         ;; r = 0: the one-arc walk i, j
         (function/lam
          [['hr (rounds-below 'n 'D 'P nat-zero)] ['i nat] ['hi (strict-below 'i 'n)] ['j nat] ['hj (strict-below 'j 'n)]]
          (let [one (succ nat-zero)
                x (function/lam [['t nat]] (app (function/const* 'data/Nat.rec [type-level]) (function/lam [['ignored nat]] nat) 'i
                                                (function/lam [['tp nat] ['rec nat]] 'j) 't))
                d0 (D-at 'D nat-zero 'i 'j)
                ;; walk-length(D0, x, 1) = 0 + D0(i, j)
                val (equiv-sym (signed-add szero d0) d0
                               (equiv-trans (signed-add szero d0) (signed-add d0 szero) d0 (app (function/const* 'signed/add-commutative []) szero d0)
                                            (app (function/const* 'signed/add-zero-right []) d0)))
                in-r (function/lam [['t nat] ['ht (at-most 't one)]]
                                   (use-disj (eq-nat 't one) (strict-below 't one) (strict-below (app x 't) 'n)
                                             (app (function/const* 'nat/at-most-split []) 't one 'ht)
                                             (function/lam [['he (eq-nat 't one)]] (subst-nat one 't (nat-sym 't one 'he) (function/lam [['q nat]] (strict-below (app x 'q) 'n)) 'hj))
                                             (function/lam [['hl (strict-below 't one)]]
                                                           (subst-nat nat-zero 't (nat-sym 't nat-zero (@#'pigeonhole/zero-of-le-zero 't (app (function/const* 'nat/at-most-successor-cancel-local []) 't nat-zero 'hl)))
                                                                      (function/lam [['q nat]] (strict-below (app x 'q) 'n)) 'hi))))]
            (pack 'n 'D nat-zero 'i 'j one x in-r (nat-refl 'i) (nat-refl 'j) val)))
         (function/lam
          [['r nat] ['ih (claim 'n 'D 'P 'r)] ['hr (rounds-below 'n 'D 'P (succ 'r))] ['i nat] ['hi (strict-below 'i 'n)] ['j nat] ['hj (strict-below 'j 'n)]]
          (let [r1 (succ 'r) p (app 'P 'r)
                hr-now (function/lam [['t nat] ['ht (strict-below 't 'r)]] (app 'hr 't (sb-weaken 't 'r 'ht)))
                this (app 'hr 'r (sb-self 'r))
                hp (pleft (strict-below p 'n) (function/forall [['i2 nat] ['hi2 (strict-below 'i2 'n)] ['j2 nat] ['hj2 (strict-below 'j2 'n)]]
                                                               (disj* (sequiv (D-at 'D r1 'i2 'j2) (D-at 'D 'r 'i2 'j2))
                                                                      (sequiv (D-at 'D r1 'i2 'j2) (signed-add (D-at 'D 'r 'i2 p) (D-at 'D 'r p 'j2)))))
                          this)
                either (app (pright (strict-below p 'n) (function/forall [['i2 nat] ['hi2 (strict-below 'i2 'n)] ['j2 nat] ['hj2 (strict-below 'j2 'n)]]
                                                                         (disj* (sequiv (D-at 'D r1 'i2 'j2) (D-at 'D 'r 'i2 'j2))
                                                                                (sequiv (D-at 'D r1 'i2 'j2) (signed-add (D-at 'D 'r 'i2 p) (D-at 'D 'r p 'j2)))))
                                    this)
                            'i 'hi 'j 'hj)
                goal (realised 'n 'D r1 'i 'j)
                new (D-at 'D r1 'i 'j)]
            (use-disj (sequiv new (D-at 'D 'r 'i 'j)) (sequiv new (signed-add (D-at 'D 'r 'i p) (D-at 'D 'r p 'j))) goal either
                      ;; kept: the previous walk
                      (function/lam
                       [['hk (sequiv new (D-at 'D 'r 'i 'j))]]
                       (unpack 'n 'D 'r 'i 'j (app 'ih hr-now 'i 'hi 'j 'hj) goal "keep"
                               (fn [k x hin h0 hkk hv]
                                 (pack 'n 'D r1 'i 'j k x hin h0 hkk (equiv-trans new (D-at 'D 'r 'i 'j) (walk-length (W0 'D) x k) 'hk hv)))))
                      ;; through the pivot: concatenate i -> p and p -> j
                      (function/lam
                       [['hv2 (sequiv new (signed-add (D-at 'D 'r 'i p) (D-at 'D 'r p 'j)))]]
                       (unpack 'n 'D 'r 'i p (app 'ih hr-now 'i 'hi p hp) goal "left"
                               (fn [k1 x hin1 h01 hk1 hvx]
                                 (unpack 'n 'D 'r p 'j (app 'ih hr-now p hp 'j 'hj) goal "right"
                                         (fn [k2 y hin2 h02 hk2 hvy]
                                           (let [join (nat-trans (app x k1) p (app y nat-zero) hk1 (nat-sym (app y nat-zero) p h02))
                                                 z (walk-concat/concat-walk x k1 y)
                                                 cc (app (function/const* 'signed/walk-concat []) (W0 'D) x k1 y k2 join)
                                                 kz (nadd k2 k1)
                                                 lz (walk-length (W0 'D) z kz)
                                                 sum-xy (signed-add (walk-length (W0 'D) x k1) (walk-length (W0 'D) y k2))
                                                 r1c (conj* (eq-nat (app z kz) (app y k2)) (sequiv lz sum-xy))
                                                 z0 (pleft (eq-nat (app z nat-zero) (app x nat-zero)) r1c cc)
                                                 zk (pleft (eq-nat (app z kz) (app y k2)) (sequiv lz sum-xy) (pright (eq-nat (app z nat-zero) (app x nat-zero)) r1c cc))
                                                 zl (pright (eq-nat (app z kz) (app y k2)) (sequiv lz sum-xy) (pright (eq-nat (app z nat-zero) (app x nat-zero)) r1c cc))
                                                 value (equiv-trans new (signed-add (D-at 'D 'r 'i p) (D-at 'D 'r p 'j)) lz 'hv2
                                                                    (equiv-trans (signed-add (D-at 'D 'r 'i p) (D-at 'D 'r p 'j)) sum-xy lz
                                                                                 (add-respects (D-at 'D 'r 'i p) (walk-length (W0 'D) x k1) (D-at 'D 'r p 'j) (walk-length (W0 'D) y k2) hvx hvy)
                                                                                 (equiv-sym lz sum-xy zl)))]
                                             (pack 'n 'D r1 'i 'j kz z
                                                   (app (function/const* 'nat/walk-concat-range []) 'n x k1 y k2 join hin1 hin2)
                                                   (nat-trans (app z nat-zero) (app x nat-zero) 'i z0 h01)
                                                   (nat-trans (app z kz) (app y k2) 'j zk hk2)
                                                   value))))))))))
         'r))})

(def theorem-specs [attained-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      walk-concat/extend-environment
      walk-shorten/extend-environment
      (support/extend-with :fw-convergence-attained theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
