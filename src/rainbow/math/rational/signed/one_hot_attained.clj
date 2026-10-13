(ns rainbow.math.rational.signed.one-hot-attained
  "THE ONE-HOT SELECTOR / ATTAINMENT LEMMA, the shared Level-3 reading of every checker that
  certifies a minimum or maximum with a 0/1 witness (the max/min-type checks).

  Such a checker proves each candidate's GAP is nonnegative (the certified value is a bound of
  every candidate), the witness weights are 0/1 and sum to 1, and the witness-weighted gaps sum
  to 0. The reading is that the witnessed candidate is ATTAINED:

     signed/one-hot-attained :
       forall W G k,
       (forall i < k, 0 <= W i) -> (forall i < k, W i ~ 0 \\/ W i ~ 1) ->
       (forall i < k, 0 <= G i) ->
       expr-sum-value W k ~ 1 -> expr-sum-value (fun i. W i * G i) k ~ 0 ->
       exists i, i < k /\\ W i ~ 1 /\\ G i ~ 0

  `0 <= W i` follows from the 0/1 disjunction and is taken as a hypothesis for brevity. `0 <= G i`
  is NOT needed for the statement to be true: 0/1 weights summing to 1 select exactly one
  candidate, and the weighted sum is that candidate's gap. This proof's induction uses it, and every
  one-hot checker supplies it (its bound groups), so the hypothesis costs no consumer anything.
  Dropping it would need a counting argument instead. Proof, by induction on k with a strengthened claim: the
  weighted sum S_k is >= 0, and if S_k ~ 0 then either the weights so far sum to ~ 0 or a
  selected candidate below k is attained. A step splits S_{k+1} = S_k + W_k G_k ~ 0 into two
  zero parts (both are nonnegative). If the earlier weights sum to 0, either W_k ~ 0 (the total
  stays 0) or W_k ~ 1 (then G_k ~ W_k G_k ~ 0, attained at k). At the end the weights sum to
  1, not 0, which leaves attainment. The sum facts used here are proved inside this induction;
  the general expr-sum-value algebra is a separate lane."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.checks :as checker]
            [rainbow.math.rational.signed.add-zero-reflection :as zero-reflection]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.no-zero-divisors :as no-zero-divisors]
            [rainbow.math.rational.signed.order-monotone :as order-monotone]
            [rainbow.math.rational.signed.limit-uniqueness :as limit-uniqueness]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.nat.strict-below-more :as strict-more]))

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
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- add-respects [a ah b bh e1 e2] (app (function/const* 'signed/add-respects-equivalence []) a ah b bh e1 e2))
(defn- mul-respects [a ah b bh e1 e2] (app (function/const* 'signed/multiply-respects-equivalence []) a ah b bh e1 e2))
(defn- add-zero-right [a] (app (function/const* 'signed/add-zero-right []) a))
(defn- mul-zero-left [a] (app (function/const* 'signed/multiply-zero-left []) a))
(defn- mul-one-left [a] (app (function/const* 'signed/multiply-one-left []) a))
(defn- nonneg-of-le [x h] (app (function/const* 'signed/nonnegative-of-zero-at-most []) x h))
(defn- le-of-nonneg [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- mul-nonneg [a b ha hb] (app (function/const* 'signed/multiply-nonnegative []) a b ha hb))
(defn- split-left [l r hl hr hs] (app (function/const* 'signed/add-zero-split-nonnegative-left []) l r hl hr hs))
(defn- split-right [l r hl hr hs] (app (function/const* 'signed/add-zero-split-nonnegative-right []) l r hl hr hs))

(defn- W-at [W i] (app W i))
(defn- product [W G] (function/lam [['i nat]] (signed-mul (app W 'i) (app G 'i))))
(defn- all-below [k body-fn] (function/forall [['i nat] ['hi (strict-below 'i k)]] (body-fn 'i)))
(defn- attained [W G k]
  (proposition/existence type-level nat
                         (function/lam [['i nat]] (conj* (strict-below 'i k) (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero))))))
(defn- hyps [W G k body]
  (function/forall [['hw (all-below k (fn [i] (sle szero (app W i))))]
                    ['h01 (all-below k (fn [i] (disj* (sequiv (app W i) szero) (sequiv (app W i) sone))))]
                    ['hg (all-below k (fn [i] (sle szero (app G i))))]]
                   body))
(defn- strengthened [W G k]
  (let [S (expr-sum-value (product W G) k)]
    (hyps W G k (conj* (nonneg S)
                       (function/arrow (sequiv S szero)
                                       (disj* (sequiv (expr-sum-value W k) szero) (attained W G k)))))))

(defn- lift-attained
  "exists i < k ... |- exists i < k + 1 ..."
  [W G k h]
  (let [P (fn [bound] (function/lam [['i nat]] (conj* (strict-below 'i bound) (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero)))))]
    (app h (attained W G (succ k))
         (function/lam [['i nat] ['pf (app (P k) 'i)]]
                       (let [rest (conj* (sequiv (app W 'i) sone) (sequiv (app G 'i) szero))]
                         (app (function/const* 'proposition/witness [type-level]) nat (P (succ k)) 'i
                              (conjoin (strict-below 'i (succ k)) rest
                                       (sb-weaken 'i k (pleft (strict-below 'i k) rest 'pf))
                                       (pright (strict-below 'i k) rest 'pf))))))))

(def strengthened-spec
  {:name 'signed/one-hot-attained-strengthened :universes []
   :type (function/forall [['W val-type] ['G val-type] ['k nat]] (strengthened 'W 'G 'k))
   :value
   (function/lam
    [['W val-type] ['G val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (strengthened 'W 'G 'kk))
         ;; k = 0: S = 0 is nonnegative; the weights sum to 0
         (function/lam
          [['hw (all-below nat-zero (fn [i] (sle szero (app 'W i))))]
           ['h01 (all-below nat-zero (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
           ['hg (all-below nat-zero (fn [i] (sle szero (app 'G i))))]]
          (conjoin (nonneg szero)
                   (function/arrow (sequiv szero szero) (disj* (sequiv szero szero) (attained 'W 'G nat-zero)))
                   (nonneg-of-le szero (app (function/const* 'signed/at-most-reflexive []) szero))
                   (function/lam [['hz (sequiv szero szero)]]
                                 (left-disj (sequiv szero szero) (attained 'W 'G nat-zero) (equiv-refl szero)))))
         (function/lam
          [['k nat] ['ih (strengthened 'W 'G 'k)]
           ['hw (all-below (succ 'k) (fn [i] (sle szero (app 'W i))))]
           ['h01 (all-below (succ 'k) (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
           ['hg (all-below (succ 'k) (fn [i] (sle szero (app 'G i))))]]
          (let [k 'k k1 (succ 'k)
                Wk (app 'W k) Gk (app 'G k) t (signed-mul Wk Gk)
                S (expr-sum-value (product 'W 'G) k) SW (expr-sum-value 'W k)
                weaken (fn [h body-fn] (function/lam [['i nat] ['hi (strict-below 'i k)]] (app h 'i (sb-weaken 'i k 'hi))))
                ih-now (app 'ih (weaken 'hw nil) (weaken 'h01 nil) (weaken 'hg nil))
                S-nonneg (pleft (nonneg S) (function/arrow (sequiv S szero) (disj* (sequiv SW szero) (attained 'W 'G k))) ih-now)
                S-reading (pright (nonneg S) (function/arrow (sequiv S szero) (disj* (sequiv SW szero) (attained 'W 'G k))) ih-now)
                Wk-nonneg (nonneg-of-le Wk (app 'hw k (sb-self k)))
                Gk-nonneg (nonneg-of-le Gk (app 'hg k (sb-self k)))
                t-nonneg (mul-nonneg Wk Gk Wk-nonneg Gk-nonneg)
                S1 (signed-add S t) SW1 (signed-add SW Wk)
                ;; 0 + 0 <= S + t, and 0 + 0 ~ 0
                S1-le (app (function/const* 'signed/add-monotone []) szero S szero t (le-of-nonneg S S-nonneg) (le-of-nonneg t t-nonneg))
                S1-nonneg (nonneg-of-le S1 (app (function/const* 'signed/at-most-respects-equivalence [])
                                                (signed-add szero szero) szero S1 S1 (add-zero-right szero) (equiv-refl S1) S1-le))
                goal (disj* (sequiv SW1 szero) (attained 'W 'G k1))
                reading
                (function/lam
                 [['hz (sequiv S1 szero)]]
                 (let [S-zero (split-left S t S-nonneg t-nonneg 'hz)
                       t-zero (split-right S t S-nonneg t-nonneg 'hz)]
                   (use-disj (sequiv SW szero) (attained 'W 'G k) goal (app S-reading S-zero)
                             ;; the earlier weights sum to 0: decide on W_k
                             (function/lam
                              [['hsw (sequiv SW szero)]]
                              (use-disj (sequiv Wk szero) (sequiv Wk sone) goal (app 'h01 k (sb-self k))
                                        ;; W_k ~ 0: SW + W_k ~ 0 + 0 ~ 0
                                        (function/lam
                                         [['hw0 (sequiv Wk szero)]]
                                         (left-disj (sequiv SW1 szero) (attained 'W 'G k1)
                                                    (equiv-trans SW1 (signed-add szero szero) szero
                                                                 (add-respects SW szero Wk szero 'hsw 'hw0) (add-zero-right szero))))
                                        ;; W_k ~ 1: G_k ~ 1 * G_k ~ W_k * G_k = t ~ 0, attained at k
                                        (function/lam
                                         [['hw1 (sequiv Wk sone)]]
                                         (let [g-zero (equiv-trans Gk (signed-mul sone Gk) szero
                                                                   (equiv-sym (signed-mul sone Gk) Gk (mul-one-left Gk))
                                                                   (equiv-trans (signed-mul sone Gk) t szero
                                                                                (mul-respects sone Wk Gk Gk (equiv-sym Wk sone 'hw1) (equiv-refl Gk))
                                                                                t-zero))
                                               rest (conj* (sequiv Wk sone) (sequiv Gk szero))]
                                           (right-disj (sequiv SW1 szero) (attained 'W 'G k1)
                                                       (app (function/const* 'proposition/witness [type-level]) nat
                                                            (function/lam [['i nat]] (conj* (strict-below 'i k1) (conj* (sequiv (app 'W 'i) sone) (sequiv (app 'G 'i) szero))))
                                                            k (conjoin (strict-below k k1) rest (sb-self k) (conjoin (sequiv Wk sone) (sequiv Gk szero) 'hw1 g-zero))))))))
                             ;; attained below k already
                             (function/lam [['ha (attained 'W 'G k)]]
                                           (right-disj (sequiv SW1 szero) (attained 'W 'G k1) (lift-attained 'W 'G k 'ha))))))]
            (conjoin (nonneg S1) (function/arrow (sequiv S1 szero) goal) S1-nonneg reading)))
         'k))})

(def attained-spec
  {:name 'signed/one-hot-attained :universes []
   :type (function/forall
          [['W val-type] ['G val-type] ['k nat]
           ['hw (all-below 'k (fn [i] (sle szero (app 'W i))))]
           ['h01 (all-below 'k (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
           ['hg (all-below 'k (fn [i] (sle szero (app 'G i))))]
           ['hsum (sequiv (expr-sum-value 'W 'k) sone)]
           ['hzero (sequiv (expr-sum-value (product 'W 'G) 'k) szero)]]
          (attained 'W 'G 'k))
   :value
   (function/lam
    [['W val-type] ['G val-type] ['k nat]
     ['hw (all-below 'k (fn [i] (sle szero (app 'W i))))]
     ['h01 (all-below 'k (fn [i] (disj* (sequiv (app 'W i) szero) (sequiv (app 'W i) sone))))]
     ['hg (all-below 'k (fn [i] (sle szero (app 'G i))))]
     ['hsum (sequiv (expr-sum-value 'W 'k) sone)]
     ['hzero (sequiv (expr-sum-value (product 'W 'G) 'k) szero)]]
    (let [S (expr-sum-value (product 'W 'G) 'k) SW (expr-sum-value 'W 'k)
          st (app (function/const* 'signed/one-hot-attained-strengthened []) 'W 'G 'k 'hw 'h01 'hg)
          reading (pright (nonneg S) (function/arrow (sequiv S szero) (disj* (sequiv SW szero) (attained 'W 'G 'k))) st)]
      (use-disj (sequiv SW szero) (attained 'W 'G 'k) (attained 'W 'G 'k) (app reading 'hzero)
                (function/lam [['hsw (sequiv SW szero)]]
                              (explode (attained 'W 'G 'k)
                                       (app (function/const* 'signed/one-not-equivalent-zero [])
                                            (equiv-trans sone SW szero (equiv-sym SW sone 'hsum) 'hsw))))
                (function/lam [['ha (attained 'W 'G 'k)]] 'ha))))})

(def theorem-specs [strengthened-spec attained-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      checker/extend-environment
      strict-more/extend-environment
      zero-reflection/extend-environment
      multiply-order/extend-environment
      multiply-ring/extend-environment
      unit-laws/extend-environment
      no-zero-divisors/extend-environment
      order-monotone/extend-environment
      limit-uniqueness/extend-environment
      map-sum/extend-environment
      (support/extend-with :signed-one-hot-attained theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
