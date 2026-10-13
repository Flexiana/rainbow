(ns rainbow.math.rational.signed.one-hot-keep
  "THE ONE-HOT ATTAINMENT LEMMA WITH A KEEP OPTION, in the sign convention the relaxation checkers
  use (Bellman-Ford round, Dijkstra step, Floyd-Warshall round). Such a checker certifies a new value v' as the minimum of a 'keep' candidate and k
  arc candidates. v' is a lower bound of each, so every GAP v' - candidate is <= 0. A 0/1 witness
  y (keep) and Z_i (arc i) sums to 1, and the witnessed gaps sum to 0:

     signed/one-hot-keep-attained :
       0 <= y, y ~ 0 \\/ y ~ 1, a <= 0,
       (forall i < k, 0 <= Z i), (forall i < k, Z i ~ 0 \\/ Z i ~ 1), (forall i < k, B i <= 0),
       y + expr-sum-value Z k ~ 1,  y * a + expr-sum-value (fun i. Z i * B i) k ~ 0
       ->  (y ~ 1 /\\ a ~ 0)  \\/  exists i < k, Z i ~ 1 /\\ B i ~ 0

  so the minimum is attained at the keep candidate or at a witnessed arc. The proof is the same
  strengthened induction as signed/one-hot-attained with the order reversed: a sum of nonpositive
  terms is <= 0, and two nonpositive terms adding to ~ 0 are both ~ 0. That last step is proved
  here from the order laws (0 ~ a + b <= a + 0 ~ a, then antisymmetry)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.one-hot-attained :as one-hot]))

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
(defn- signed-mul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nonneg [a] (app (function/const* 'signed/nonnegative []) a))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- add-respects [a ah b bh e1 e2] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh e1 e2))
(defn- mul-respects [a ah b bh e1 e2] (app (function/const* 'signed/multiply-respects-equivalence []) a ah b bh e1 e2))
(defn- add-zero-right [a] (app (function/const* 'signed/add-zero-right []) a))
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- mul-one-left [a] (app (function/const* 'signed/multiply-one-left []) a))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-refl [a] (app (function/const* 'signed/at-most-reflexive []) a))
(defn- antisym [a b h1 h2] (app (function/const* 'signed/at-most-antisymmetric []) a b h1 h2))
(defn- nonneg-of-le [x h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) x h))
(defn- le-zero-of-nonpos [x h] (app (function/const* 'signed/at-most-zero-of-nonpositive []) x h))
(defn- mul-nonneg-nonpos [a b ha hb] (app (function/const* 'signed/multiply-nonnegative-nonpositive []) a b ha hb))
(defn- nonpos-of-le [x h] (app (function/const* 'signed/nonpositive-of-at-most-zero []) x h))

(defn- zero-plus [a]
  "0 + a ~ a"
  (equiv-trans (signed-add szero a) (signed-add a szero) a (add-comm szero a) (add-zero-right a)))

(defn- split-left
  "a <= 0, b <= 0, a + b ~ 0 |- a ~ 0:  0 ~ a + b <= a + 0 ~ a, so 0 <= a."
  [a b ha hb hs]
  (let [up (app (function/const* 'signed/add-left-monotone []) b szero a hb)                 ; a + b <= a + 0
        zero-le-a (le-respects (signed-add a b) szero (signed-add a szero) a hs (add-zero-right a) up)]
    (antisym a szero ha zero-le-a)))

(defn- split-right
  "a <= 0, b <= 0, a + b ~ 0 |- b ~ 0:  0 ~ a + b <= 0 + b ~ b."
  [a b ha hb hs]
  (let [up (app (function/const* 'signed/add-right-monotone []) a szero b ha)                ; a + b <= 0 + b
        zero-le-b (le-respects (signed-add a b) szero (signed-add szero b) b hs (zero-plus b) up)]
    (antisym b szero hb zero-le-b)))

(defn- sum-nonpos
  "a <= 0, b <= 0 |- a + b <= 0"
  [a b ha hb]
  (le-respects (signed-add a b) (signed-add a b) (signed-add szero szero) szero (equiv-refl (signed-add a b)) (add-zero-right szero)
               (app (function/const* 'signed/add-monotone []) a szero b szero ha hb)))

(defn- product [W G] (function/lam [['i nat]] (signed-mul (app W 'i) (app G 'i))))
(defn- all-below [k body-fn] (function/forall [['i nat] ['hi (strict-below 'i k)]] (body-fn 'i)))
(defn- attained [W G k]
  (proposition/existence type-level nat
                         (function/lam [['i nat]] (conj* (strict-below 'i k) (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero))))))
(defn- strengthened [W B k]
  (let [S (expr-sum-value (product W B) k)]
    (function/forall [['hw (all-below k (fn [i] (sle szero (app W i))))]
                      ['h01 (all-below k (fn [i] (disj* (sequiv (app W i) szero) (sequiv (app W i) sone))))]
                      ['hb (all-below k (fn [i] (sle (app B i) szero)))]]
                     (conj* (sle S szero)
                            (function/arrow (sequiv S szero) (disj* (sequiv (expr-sum-value W k) szero) (attained W B k)))))))

(defn- lift-attained [W G k h]
  (let [P (fn [bound] (function/lam [['i nat]] (conj* (strict-below 'i bound) (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero)))))]
    (app h (attained W G (succ k))
         (function/lam [['i nat] ['pf (app (P k) 'i)]]
                       (let [rest (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero))]
                         (app (function/const* 'proposition/witness [type-level]) nat (P (succ k)) 'i
                              (conjoin (strict-below 'i (succ k)) rest
                                       (sb-weaken 'i k (pleft (strict-below 'i k) rest 'pf))
                                       (pright (strict-below 'i k) rest 'pf))))))))

(def nonpositive-strengthened-spec
  {:name 'signed/one-hot-attained-nonpositive-strengthened :universes []
   :type (function/forall [['W val-type] ['B val-type] ['k nat]] (strengthened 'W 'B 'k))
   :value
   (function/lam
    [['W val-type] ['B val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (strengthened 'W 'B 'kk))
         (function/lam
          [['hw (all-below nat-zero (fn [i] (sle szero (app 'W i))))]
           ['h01 (all-below nat-zero (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
           ['hb (all-below nat-zero (fn [i] (sle (app 'B i) szero)))]]
          (conjoin (sle szero szero)
                   (function/arrow (sequiv szero szero) (disj* (sequiv szero szero) (attained 'W 'B nat-zero)))
                   (le-refl szero)
                   (function/lam [['hz (sequiv szero szero)]]
                                 (left-disj (sequiv szero szero) (attained 'W 'B nat-zero) (equiv-refl szero)))))
         (function/lam
          [['k nat] ['ih (strengthened 'W 'B 'k)]
           ['hw (all-below (succ 'k) (fn [i] (sle szero (app 'W i))))]
           ['h01 (all-below (succ 'k) (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
           ['hb (all-below (succ 'k) (fn [i] (sle (app 'B i) szero)))]]
          (let [k 'k k1 (succ 'k)
                Wk (app 'W k) Bk (app 'B k) t (signed-mul Wk Bk)
                S (expr-sum-value (product 'W 'B) k) SW (expr-sum-value 'W k)
                weaken (fn [h] (function/lam [['i nat] ['hi (strict-below 'i k)]] (app h 'i (sb-weaken 'i k 'hi))))
                ih-now (app 'ih (weaken 'hw) (weaken 'h01) (weaken 'hb))
                claim-k (function/arrow (sequiv S szero) (disj* (sequiv SW szero) (attained 'W 'B k)))
                S-le (pleft (sle S szero) claim-k ih-now)
                S-reading (pright (sle S szero) claim-k ih-now)
                t-le (le-zero-of-nonpos t (mul-nonneg-nonpos Wk Bk (nonneg-of-le Wk (app 'hw k (sb-self k)))
                                                             (nonpos-of-le Bk (app 'hb k (sb-self k)))))
                S1 (signed-add S t) SW1 (signed-add SW Wk)
                goal (disj* (sequiv SW1 szero) (attained 'W 'B k1))
                reading
                (function/lam
                 [['hz (sequiv S1 szero)]]
                 (let [S-zero (split-left S t S-le t-le 'hz)
                       t-zero (split-right S t S-le t-le 'hz)]
                   (use-disj (sequiv SW szero) (attained 'W 'B k) goal (app S-reading S-zero)
                             (function/lam
                              [['hsw (sequiv SW szero)]]
                              (use-disj (sequiv Wk szero) (sequiv Wk sone) goal (app 'h01 k (sb-self k))
                                        (function/lam
                                         [['hw0 (sequiv Wk szero)]]
                                         (left-disj (sequiv SW1 szero) (attained 'W 'B k1)
                                                    (equiv-trans SW1 (signed-add szero szero) szero
                                                                 (add-respects SW szero Wk szero 'hsw 'hw0) (add-zero-right szero))))
                                        (function/lam
                                         [['hw1 (sequiv Wk sone)]]
                                         (let [b-zero (equiv-trans Bk (signed-mul sone Bk) szero
                                                                   (equiv-sym (signed-mul sone Bk) Bk (mul-one-left Bk))
                                                                   (equiv-trans (signed-mul sone Bk) t szero
                                                                                (mul-respects sone Wk Bk Bk (equiv-sym Wk sone 'hw1) (equiv-refl Bk))
                                                                                t-zero))
                                               rest (conj* (sequiv Wk sone) (sequiv Bk szero))]
                                           (right-disj (sequiv SW1 szero) (attained 'W 'B k1)
                                                       (app (function/const* 'proposition/witness [type-level]) nat
                                                            (function/lam [['i nat]] (conj* (strict-below 'i k1) (conj* (sequiv (app 'W 'i) sone) (sequiv (app 'B 'i) szero))))
                                                            k (conjoin (strict-below k k1) rest (sb-self k) (conjoin (sequiv Wk sone) (sequiv Bk szero) 'hw1 b-zero))))))))
                             (function/lam [['ha (attained 'W 'B k)]]
                                           (right-disj (sequiv SW1 szero) (attained 'W 'B k1) (lift-attained 'W 'B k 'ha))))))]
            (conjoin (sle S1 szero) (function/arrow (sequiv S1 szero) goal) (sum-nonpos S t S-le t-le) reading)))
         'k))})

(defn- keep-goal [y a Z B k] (disj* (conj* (sequiv y sone) (sequiv a szero)) (attained Z B k)))

(def keep-attained-spec
  {:name 'signed/one-hot-keep-attained :universes []
   :type (function/forall
          [['y signed] ['a signed] ['Z val-type] ['B val-type] ['k nat]
           ['hy (sle szero 'y)] ['hy01 (disj* (sequiv 'y szero) (sequiv 'y sone))] ['ha (sle 'a szero)]
           ['hz (all-below 'k (fn [i] (sle szero (app 'Z i))))]
           ['hz01 (all-below 'k (fn [i] (disj* (sequiv (app 'Z i) szero) (sequiv (app 'Z i) sone))))]
           ['hb (all-below 'k (fn [i] (sle (app 'B i) szero)))]
           ['hsum (sequiv (signed-add 'y (expr-sum-value 'Z 'k)) sone)]
           ['hzero (sequiv (signed-add (signed-mul 'y 'a) (expr-sum-value (product 'Z 'B) 'k)) szero)]]
          (keep-goal 'y 'a 'Z 'B 'k))
   :value
   (function/lam
    [['y signed] ['a signed] ['Z val-type] ['B val-type] ['k nat]
     ['hy (sle szero 'y)] ['hy01 (disj* (sequiv 'y szero) (sequiv 'y sone))] ['ha (sle 'a szero)]
     ['hz (all-below 'k (fn [i] (sle szero (app 'Z i))))]
     ['hz01 (all-below 'k (fn [i] (disj* (sequiv (app 'Z i) szero) (sequiv (app 'Z i) sone))))]
     ['hb (all-below 'k (fn [i] (sle (app 'B i) szero)))]
     ['hsum (sequiv (signed-add 'y (expr-sum-value 'Z 'k)) sone)]
     ['hzero (sequiv (signed-add (signed-mul 'y 'a) (expr-sum-value (product 'Z 'B) 'k)) szero)]]
    (let [P (signed-mul 'y 'a) S (expr-sum-value (product 'Z 'B) 'k) SZ (expr-sum-value 'Z 'k)
          st (app (function/const* 'signed/one-hot-attained-nonpositive-strengthened []) 'Z 'B 'k 'hz 'hz01 'hb)
          claim (function/arrow (sequiv S szero) (disj* (sequiv SZ szero) (attained 'Z 'B 'k)))
          S-le (pleft (sle S szero) claim st)
          P-le (le-zero-of-nonpos P (mul-nonneg-nonpos 'y 'a (nonneg-of-le 'y 'hy) (nonpos-of-le 'a 'ha)))
          P-zero (split-left P S P-le S-le 'hzero)
          S-zero (split-right P S P-le S-le 'hzero)
          goal (keep-goal 'y 'a 'Z 'B 'k)]
      (use-disj (sequiv SZ szero) (attained 'Z 'B 'k) goal (app (pright (sle S szero) claim st) S-zero)
                ;; the arcs carry no weight: y ~ y + 0 ~ y + SZ ~ 1, then a ~ 1 * a ~ y * a ~ 0
                (function/lam
                 [['hsz (sequiv SZ szero)]]
                 (let [y-one (equiv-trans 'y (signed-add 'y szero) sone
                                          (equiv-sym (signed-add 'y szero) 'y (add-zero-right 'y))
                                          (equiv-trans (signed-add 'y szero) (signed-add 'y SZ) sone
                                                       (add-respects 'y 'y szero SZ (equiv-refl 'y) (equiv-sym SZ szero 'hsz))
                                                       'hsum))
                       a-zero (equiv-trans 'a (signed-mul sone 'a) szero
                                           (equiv-sym (signed-mul sone 'a) 'a (mul-one-left 'a))
                                           (equiv-trans (signed-mul sone 'a) P szero
                                                        (mul-respects sone 'y 'a 'a (equiv-sym 'y sone y-one) (equiv-refl 'a))
                                                        P-zero))]
                   (left-disj (conj* (sequiv 'y sone) (sequiv 'a szero)) (attained 'Z 'B 'k)
                              (conjoin (sequiv 'y sone) (sequiv 'a szero) y-one a-zero))))
                (function/lam [['hat (attained 'Z 'B 'k)]]
                              (right-disj (conj* (sequiv 'y sone) (sequiv 'a szero)) (attained 'Z 'B 'k) 'hat)))))})

(def theorem-specs [nonpositive-strengthened-spec keep-attained-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.one-hot-attained])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-one-hot-keep theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.one-hot-keep))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
