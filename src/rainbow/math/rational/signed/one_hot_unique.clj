(ns rainbow.math.rational.signed.one-hot-unique
  "A ONE-HOT SELECTOR SELECTS ONE INDEX. Nonnegative weights summing to ~1 cannot have two distinct
  entries ~1:

     signed/term-below-sum     : (forall i < k, 0 <= S i) -> p < k -> S p <= sum S k
     signed/two-terms-below-sum: (forall i < k, 0 <= S i) -> p < q -> q < k -> S p + S q <= sum S k
     signed/one-hot-unique     : (forall i < k, 0 <= S i) -> sum S k ~ 1 -> p < k -> q < k ->
                                 S p ~ 1 -> S q ~ 1 -> p = q

  since distinct p and q would give 1 + 1 <= sum ~ 1. Consumer: the Floyd-Warshall chain bridge.
  A chain names its pivots P t, and uniqueness identifies the reading's existential pivot with them."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.one-hot-selects :as selects]
            [rainbow.math.nat.pigeonhole :as pigeonhole]
            [rainbow.math.sums.value-algebra :as algebra]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private sone (function/const* 'signed/one []))
(def ^:private val-type (function/arrow nat signed))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- add-zero-right [a] (app (function/const* 'signed/add-zero-right []) a))

(defn- nonneg-below [S k] (function/forall [['i nat] ['hi (strict-below 'i k)]] (sle szero (app S 'i))))
(defn- weaken-nonneg [S k h] (function/lam [['i nat] ['hi (strict-below 'i k)]] (app h 'i (sb-weaken 'i k 'hi))))
(defn- grow
  "sum S k <= sum S (k + 1) when 0 <= S k:  sum + 0 <= sum + S k"
  [S k hSk]
  (le-respects (signed-add (expr-sum-value S k) szero) (expr-sum-value S k) (expr-sum-value S (succ k)) (expr-sum-value S (succ k))
               (add-zero-right (expr-sum-value S k)) (equiv-refl (expr-sum-value S (succ k)))
               (app (function/const* 'signed/add-left-monotone []) szero (app S k) (expr-sum-value S k) hSk)))

(defn- term-claim [S k] (function/forall [['hn (nonneg-below S k)] ['p nat] ['hp (strict-below 'p k)]] (sle (app S 'p) (expr-sum-value S k))))

(defn- sum-nonneg
  "0 <= sum S k, by signed/expr-sum-value-monotone-below against the zero function"
  [S k hn]
  (let [z (function/lam [['zi nat]] szero)]
    (le-respects (expr-sum-value z k) szero (expr-sum-value S k) (expr-sum-value S k)
                 (app (function/const* 'signed/expr-sum-value-zero []) k) (equiv-refl (expr-sum-value S k))
                 (app (function/const* 'signed/expr-sum-value-monotone-below []) z S k hn))))

(def term-below-spec
  {:name 'signed/term-below-sum :universes []
   :type (function/forall [['S val-type] ['k nat]] (term-claim 'S 'k))
   :value
   (function/lam
    [['S val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (term-claim 'S 'kk))
         (function/lam [['hn (nonneg-below 'S nat-zero)] ['p nat] ['hp (strict-below 'p nat-zero)]]
                       (@#'pigeonhole/below-zero-absurd 'p 'hp (sle (app 'S 'p) szero)))
         (function/lam
          [['k nat] ['ih (term-claim 'S 'k)] ['hn (nonneg-below 'S (succ 'k))] ['p nat] ['hp (strict-below 'p (succ 'k))]]
          (let [k1 (succ 'k) Sk (app 'S 'k) sum-k (expr-sum-value 'S 'k) sum-k1 (expr-sum-value 'S k1)
                goal (sle (app 'S 'p) sum-k1)
                hn-k (weaken-nonneg 'S 'k 'hn)
                hSk (app 'hn 'k (app (function/const* 'nat/strict-below-self []) 'k))]
            (use-disj (eq-nat 'p 'k) (strict-below 'p 'k) goal
                      (app (function/const* 'nat/at-most-split []) 'p 'k (@#'pigeonhole/le-of-below-succ 'p 'k 'hp))
                      ;; p = k: S k ~ 0 + S k <= sum k + S k
                      (function/lam
                       [['he (eq-nat 'p 'k)]]
                       (subst-nat 'k 'p (nat-sym 'p 'k 'he) (function/lam [['zz nat]] (sle (app 'S 'zz) sum-k1))
                                  (le-respects (signed-add szero Sk) Sk sum-k1 sum-k1
                                               (equiv-trans (signed-add szero Sk) (signed-add Sk szero) Sk (app (function/const* 'signed/add-commutative []) szero Sk) (add-zero-right Sk))
                                               (equiv-refl sum-k1)
                                               (app (function/const* 'signed/add-right-monotone []) szero sum-k Sk (sum-nonneg 'S 'k hn-k)))))
                      ;; p < k: S p <= sum k <= sum (k + 1)
                      (function/lam
                       [['hl (strict-below 'p 'k)]]
                       (le-trans (app 'S 'p) sum-k sum-k1 (app 'ih hn-k 'p 'hl) (grow 'S 'k hSk))))))
         'k))})

(defn- two-claim [S k]
  (function/forall [['hn (nonneg-below S k)] ['p nat] ['q nat] ['hpq (strict-below 'p 'q)] ['hq (strict-below 'q k)]]
                   (sle (signed-add (app S 'p) (app S 'q)) (expr-sum-value S k))))

(def two-below-spec
  {:name 'signed/two-terms-below-sum :universes []
   :type (function/forall [['S val-type] ['k nat]] (two-claim 'S 'k))
   :value
   (function/lam
    [['S val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (two-claim 'S 'kk))
         (function/lam [['hn (nonneg-below 'S nat-zero)] ['p nat] ['q nat] ['hpq (strict-below 'p 'q)] ['hq (strict-below 'q nat-zero)]]
                       (@#'pigeonhole/below-zero-absurd 'q 'hq (sle (signed-add (app 'S 'p) (app 'S 'q)) szero)))
         (function/lam
          [['k nat] ['ih (two-claim 'S 'k)] ['hn (nonneg-below 'S (succ 'k))] ['p nat] ['q nat] ['hpq (strict-below 'p 'q)] ['hq (strict-below 'q (succ 'k))]]
          (let [k1 (succ 'k) Sk (app 'S 'k) sum-k (expr-sum-value 'S 'k) sum-k1 (expr-sum-value 'S k1)
                two (signed-add (app 'S 'p) (app 'S 'q))
                goal (sle two sum-k1)
                hn-k (weaken-nonneg 'S 'k 'hn)
                hSk (app 'hn 'k (app (function/const* 'nat/strict-below-self []) 'k))]
            (use-disj (eq-nat 'q 'k) (strict-below 'q 'k) goal
                      (app (function/const* 'nat/at-most-split []) 'q 'k (@#'pigeonhole/le-of-below-succ 'q 'k 'hq))
                      ;; q = k, p < k: S p + S k <= sum k + S k
                      (function/lam
                       [['he (eq-nat 'q 'k)]]
                       (let [p-lt-k (subst-nat 'q 'k 'he (function/lam [['zz nat]] (strict-below 'p 'zz)) 'hpq)]
                         (subst-nat 'k 'q (nat-sym 'q 'k 'he) (function/lam [['zz nat]] (sle (signed-add (app 'S 'p) (app 'S 'zz)) sum-k1))
                                    (app (function/const* 'signed/add-right-monotone []) (app 'S 'p) sum-k Sk
                                         (app (function/const* 'signed/term-below-sum []) 'S 'k hn-k 'p p-lt-k)))))
                      ;; q < k: the pair sits below sum k <= sum (k + 1)
                      (function/lam
                       [['hl (strict-below 'q 'k)]]
                       (le-trans two sum-k sum-k1 (app 'ih hn-k 'p 'q 'hpq 'hl) (grow 'S 'k hSk))))))
         'k))})

(def unique-spec
  {:name 'signed/one-hot-unique :universes []
   :type (function/forall [['S val-type] ['k nat] ['hn (nonneg-below 'S 'k)] ['hsum (sequiv (expr-sum-value 'S 'k) sone)]
                           ['p nat] ['q nat] ['hp (strict-below 'p 'k)] ['hq (strict-below 'q 'k)]
                           ['sp (sequiv (app 'S 'p) sone)] ['sq (sequiv (app 'S 'q) sone)]]
                          (eq-nat 'p 'q))
   :value
   (function/lam
    [['S val-type] ['k nat] ['hn (nonneg-below 'S 'k)] ['hsum (sequiv (expr-sum-value 'S 'k) sone)]
     ['p nat] ['q nat] ['hp (strict-below 'p 'k)] ['hq (strict-below 'q 'k)]
     ['sp (sequiv (app 'S 'p) sone)] ['sq (sequiv (app 'S 'q) sone)]]
    (let [goal (eq-nat 'p 'q) sum (expr-sum-value 'S 'k) two (signed-add sone sone)
          ;; 1 + 1 <= sum ~ 1 = 1 + 0 gives 1 <= 0
          absurd (fn [pair-le e-pair]
                   (let [le (le-respects (signed-add (app 'S 'p) (app 'S 'q)) (signed-add sone sone) sum (signed-add sone szero)
                                         e-pair
                                         (equiv-trans sum sone (signed-add sone szero) 'hsum (equiv-sym (signed-add sone szero) sone (add-zero-right sone)))
                                         pair-le)]
                     (explode goal (app (function/const* 'signed/one-not-at-most-zero [])
                                        (app (function/const* 'signed/at-most-add-left-cancel []) sone szero sone le)))))
          e-pq (app (function/const* 'signed/add-respects-equivalence []) (app 'S 'p) sone (app 'S 'q) sone 'sp 'sq)
          e-qp (equiv-trans (signed-add (app 'S 'p) (app 'S 'q)) (signed-add (app 'S 'q) (app 'S 'p)) two
                            (app (function/const* 'signed/add-commutative []) (app 'S 'p) (app 'S 'q))
                            (app (function/const* 'signed/add-respects-equivalence []) (app 'S 'q) sone (app 'S 'p) sone 'sq 'sp))]
      (use-disj (strict-below 'p 'q) (disj* (eq-nat 'p 'q) (strict-below 'q 'p)) goal (app (function/const* 'nat/trichotomy []) 'p 'q)
                (function/lam [['h (strict-below 'p 'q)]] (absurd (app (function/const* 'signed/two-terms-below-sum []) 'S 'k 'hn 'p 'q 'h 'hq) e-pq))
                (function/lam
                 [['h (disj* (eq-nat 'p 'q) (strict-below 'q 'p))]]
                 (use-disj (eq-nat 'p 'q) (strict-below 'q 'p) goal 'h
                           (function/lam [['he (eq-nat 'p 'q)]] 'he)
                           (function/lam [['hl (strict-below 'q 'p)]]
                                         (let [le-qp (app (function/const* 'signed/two-terms-below-sum []) 'S 'k 'hn 'q 'p 'hl 'hp)
                                               le-pq (le-respects (signed-add (app 'S 'q) (app 'S 'p)) (signed-add (app 'S 'p) (app 'S 'q)) sum sum
                                                                  (app (function/const* 'signed/add-commutative []) (app 'S 'q) (app 'S 'p)) (equiv-refl sum) le-qp)]
                                           (absurd le-pq e-pq))))))))})

(def theorem-specs [term-below-spec two-below-spec unique-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.one-hot-selects rainbow.math.nat.pigeonhole rainbow.math.sums.value-algebra])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-one-hot-unique theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.one-hot-unique))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
