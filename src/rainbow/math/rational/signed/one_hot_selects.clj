(ns rainbow.math.rational.signed.one-hot-selects
  "THE ONE-HOT VALUE SELECTOR, the shared Level-3 reading of every checker that pins a value to a
  one-hot sum: Floyd-Warshall's pivot column and row,
  Dijkstra's chosen label and row, and the rest. 0/1 weights summing to 1 select one index, and
  every weighted sum then reads that index:

     signed/one-hot-selects :
       forall S k, (forall i < k, 0 <= S i) -> (forall i < k, S i ~ 0 \\/ S i ~ 1) ->
       expr-sum-value S k ~ 1 ->
       exists p, p < k /\\ S p ~ 1 /\\ forall X, expr-sum-value (fun i. S i * X i) k ~ X p

  One p serves EVERY X, so a checker's column sum and row sum over the same selector read the same
  pivot. The proof is a three-way strengthened induction. After k terms, either the weights sum to
  ~ 0 and every weighted sum is ~ 0; or they sum to ~ 1 and a selected p reads every X; or they
  sum to at least 1 + 1. A step with S k ~ 0 keeps the case; S k ~ 1 moves case 0 to case 1 at
  p = k, and cases 1 and 2 to case 2. At the end a sum of ~ 1 rules out ~ 0 (1 is not 0) and
  >= 1 + 1 (1 + 1 <= 1 would give 1 <= 0)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.one-hot-keep :as one-hot-keep]
            [rainbow.math.rational.signed.order-cancellation :as order-cancellation]))

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
(defn- add-comm [a b] (app (function/const* 'signed/add-commutative []) a b))
(defn- mul-zero-left [a] (app (function/const* 'signed/multiply-zero-left []) a))
(defn- mul-one-left [a] (app (function/const* 'signed/multiply-one-left []) a))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-refl [a] (app (function/const* 'signed/at-most-reflexive []) a))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))

(def ^:private two (signed-add sone sone))
(defn- zero-plus [a] (equiv-trans (signed-add szero a) (signed-add a szero) a (add-comm szero a) (add-zero-right a)))
(defn- weighted [S X] (function/lam [['i nat]] (signed-mul (app S 'i) (app X 'i))))
(defn- all-below [k body-fn] (function/forall [['i nat] ['hi (strict-below 'i k)]] (body-fn 'i)))
(defn- reads-all [S k p] (function/forall [['X val-type]] (sequiv (expr-sum-value (weighted S 'X) k) (app 'X p))))
(defn- selected [S k]
  (proposition/existence type-level nat
                         (function/lam [['p nat]] (conj* (strict-below 'p k) (conj* (sequiv (app S 'p) sone) (reads-all S k 'p))))))
(defn- case-zero [S k] (conj* (sequiv (expr-sum-value S k) szero)
                              (function/forall [['X val-type]] (sequiv (expr-sum-value (weighted S 'X) k) szero))))
(defn- case-one [S k] (conj* (sequiv (expr-sum-value S k) sone) (selected S k)))
(defn- case-many [S k] (sle two (expr-sum-value S k)))
(defn- three-way [S k] (disj* (case-zero S k) (disj* (case-one S k) (case-many S k))))
(defn- claim [S k]
  (function/forall [['hs (all-below k (fn [i] (sle szero (app S i))))]
                    ['h01 (all-below k (fn [i] (disj* (sequiv (app S i) szero) (sequiv (app S i) sone))))]]
                   (three-way S k)))

(def strengthened-spec
  {:name 'signed/one-hot-selects-strengthened :universes []
   :type (function/forall [['S val-type] ['k nat]] (claim 'S 'k))
   :value
   (function/lam
    [['S val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (claim 'S 'kk))
         ;; k = 0: both sums are 0
         (function/lam
          [['hs (all-below nat-zero (fn [i] (sle szero (app 'S i))))]
           ['h01 (all-below nat-zero (fn [i] (disj* (sequiv (app 'S i) szero) (sequiv (app 'S i) sone))))]]
          (left-disj (case-zero 'S nat-zero) (disj* (case-one 'S nat-zero) (case-many 'S nat-zero))
                     (conjoin (sequiv szero szero) (function/forall [['X val-type]] (sequiv szero szero))
                              (equiv-refl szero) (function/lam [['X val-type]] (equiv-refl szero)))))
         (function/lam
          [['k nat] ['ih (claim 'S 'k)]
           ['hs (all-below (succ 'k) (fn [i] (sle szero (app 'S i))))]
           ['h01 (all-below (succ 'k) (fn [i] (disj* (sequiv (app 'S i) szero) (sequiv (app 'S i) sone))))]]
          (let [k 'k k1 (succ 'k) Sk (app 'S k)
                sum (fn [kk] (expr-sum-value 'S kk)) wsum (fn [X kk] (expr-sum-value (weighted 'S X) kk))
                weaken (fn [h] (function/lam [['i nat] ['hi (strict-below 'i k)]] (app h 'i (sb-weaken 'i k 'hi))))
                before (app 'ih (weaken 'hs) (weaken 'h01))
                goal (three-way 'S k1)
                inj-zero (fn [p] (left-disj (case-zero 'S k1) (disj* (case-one 'S k1) (case-many 'S k1)) p))
                inj-one (fn [p] (right-disj (case-zero 'S k1) (disj* (case-one 'S k1) (case-many 'S k1))
                                            (left-disj (case-one 'S k1) (case-many 'S k1) p)))
                inj-many (fn [p] (right-disj (case-zero 'S k1) (disj* (case-one 'S k1) (case-many 'S k1))
                                             (right-disj (case-one 'S k1) (case-many 'S k1) p)))
                Sk-nonneg (app 'hs k (sb-self k))
                ;; a sum of at least two stays at least two: 2 <= s <= s + S_k
                many-grows (fn [h2] (le-trans two (sum k) (sum k1) h2
                                              (le-respects (signed-add (sum k) szero) (sum k) (sum k1) (sum k1)
                                                           (add-zero-right (sum k)) (equiv-refl (sum k1))
                                                           (app (function/const* 'signed/add-left-monotone []) szero Sk (sum k) Sk-nonneg))))
                ;; S_k ~ 0: every new weighted term is ~ 0
                on-zero
                (function/lam
                 [['h0 (sequiv Sk szero)]]
                 (let [term0 (fn [X] (equiv-trans (signed-mul Sk (app X k)) (signed-mul szero (app X k)) szero
                                                  (mul-respects Sk szero (app X k) (app X k) 'h0 (equiv-refl (app X k)))
                                                  (mul-zero-left (app X k))))
                       plus-zero (fn [a ah e] (equiv-trans (signed-add a Sk) (signed-add ah szero) ah (add-respects a ah Sk szero e 'h0) (add-zero-right ah)))
                       wplus-zero (fn [X a ah e] (equiv-trans (signed-add a (signed-mul Sk (app X k))) (signed-add ah szero) ah
                                                              (add-respects a ah (signed-mul Sk (app X k)) szero e (term0 X)) (add-zero-right ah)))]
                   (use-disj (case-zero 'S k) (disj* (case-one 'S k) (case-many 'S k)) goal before
                             (function/lam
                              [['hz (case-zero 'S k)]]
                              (let [s0 (pleft (sequiv (sum k) szero) (function/forall [['X val-type]] (sequiv (wsum 'X k) szero)) 'hz)
                                    w0 (pright (sequiv (sum k) szero) (function/forall [['X val-type]] (sequiv (wsum 'X k) szero)) 'hz)]
                                (inj-zero (conjoin (sequiv (sum k1) szero) (function/forall [['X val-type]] (sequiv (wsum 'X k1) szero))
                                                   (plus-zero (sum k) szero s0)
                                                   (function/lam [['X val-type]] (wplus-zero 'X (wsum 'X k) szero (app w0 'X)))))))
                             (function/lam
                              [['hr (disj* (case-one 'S k) (case-many 'S k))]]
                              (use-disj (case-one 'S k) (case-many 'S k) goal 'hr
                                        (function/lam
                                         [['h1 (case-one 'S k)]]
                                         (let [s1 (pleft (sequiv (sum k) sone) (selected 'S k) 'h1)
                                               sel (pright (sequiv (sum k) sone) (selected 'S k) 'h1)
                                               P (fn [bound] (function/lam [['p nat]] (conj* (strict-below 'p bound) (conj* (sequiv (app 'S 'p) sone) (reads-all 'S bound 'p)))))]
                                           (inj-one
                                            (conjoin (sequiv (sum k1) sone) (selected 'S k1)
                                                     (plus-zero (sum k) sone s1)
                                                     (app sel (selected 'S k1)
                                                          (function/lam
                                                           [['p nat] ['pf (app (P k) 'p)]]
                                                           (let [inner (conj* (sequiv (app 'S 'p) sone) (reads-all 'S k 'p))
                                                                 hp (pleft (strict-below 'p k) inner 'pf)
                                                                 sp (pleft (sequiv (app 'S 'p) sone) (reads-all 'S k 'p) (pright (strict-below 'p k) inner 'pf))
                                                                 rd (pright (sequiv (app 'S 'p) sone) (reads-all 'S k 'p) (pright (strict-below 'p k) inner 'pf))]
                                                             (app (function/const* 'proposition/witness [type-level]) nat (P k1) 'p
                                                                  (conjoin (strict-below 'p k1) (conj* (sequiv (app 'S 'p) sone) (reads-all 'S k1 'p))
                                                                           (sb-weaken 'p k hp)
                                                                           (conjoin (sequiv (app 'S 'p) sone) (reads-all 'S k1 'p) sp
                                                                                    (function/lam [['X val-type]] (wplus-zero 'X (wsum 'X k) (app 'X 'p) (app rd 'X)))))))))))))
                                        (function/lam [['h2 (case-many 'S k)]] (inj-many (many-grows 'h2))))))))
                ;; S_k ~ 1: the new weighted term reads X k
                on-one
                (function/lam
                 [['h1 (sequiv Sk sone)]]
                 (let [term1 (fn [X] (equiv-trans (signed-mul Sk (app X k)) (signed-mul sone (app X k)) (app X k)
                                                  (mul-respects Sk sone (app X k) (app X k) 'h1 (equiv-refl (app X k)))
                                                  (mul-one-left (app X k))))]
                   (use-disj (case-zero 'S k) (disj* (case-one 'S k) (case-many 'S k)) goal before
                             ;; ~0 so far: now ~1, selected at p = k
                             (function/lam
                              [['hz (case-zero 'S k)]]
                              (let [s0 (pleft (sequiv (sum k) szero) (function/forall [['X val-type]] (sequiv (wsum 'X k) szero)) 'hz)
                                    w0 (pright (sequiv (sum k) szero) (function/forall [['X val-type]] (sequiv (wsum 'X k) szero)) 'hz)
                                    sum1 (equiv-trans (sum k1) (signed-add szero sone) sone (add-respects (sum k) szero Sk sone s0 'h1) (zero-plus sone))
                                    reads (function/lam [['X val-type]]
                                                        (equiv-trans (wsum 'X k1) (signed-add szero (app 'X k)) (app 'X k)
                                                                     (add-respects (wsum 'X k) szero (signed-mul Sk (app 'X k)) (app 'X k) (app w0 'X) (term1 'X))
                                                                     (zero-plus (app 'X k))))]
                                (inj-one (conjoin (sequiv (sum k1) sone) (selected 'S k1) sum1
                                                  (app (function/const* 'proposition/witness [type-level]) nat
                                                       (function/lam [['p nat]] (conj* (strict-below 'p k1) (conj* (sequiv (app 'S 'p) sone) (reads-all 'S k1 'p))))
                                                       k (conjoin (strict-below k k1) (conj* (sequiv Sk sone) (reads-all 'S k1 k)) (sb-self k)
                                                                  (conjoin (sequiv Sk sone) (reads-all 'S k1 k) 'h1 reads)))))))
                             (function/lam
                              [['hr (disj* (case-one 'S k) (case-many 'S k))]]
                              (use-disj (case-one 'S k) (case-many 'S k) goal 'hr
                                        ;; ~1 so far: now 1 + 1
                                        (function/lam
                                         [['hone (case-one 'S k)]]
                                         (let [s1 (pleft (sequiv (sum k) sone) (selected 'S k) 'hone)
                                               e (add-respects (sum k) sone Sk sone s1 'h1)]         ; sum k1 ~ 1 + 1
                                           (inj-many (le-respects two two (sum k1) (sum k1) (equiv-refl two) (equiv-refl (sum k1))
                                                                  (le-respects (sum k1) two (sum k1) (sum k1) e (equiv-refl (sum k1)) (le-refl (sum k1)))))))
                                        (function/lam [['h2 (case-many 'S k)]] (inj-many (many-grows 'h2))))))))]
            (use-disj (sequiv Sk szero) (sequiv Sk sone) goal (app 'h01 k (sb-self k)) on-zero on-one)))
         'k))})

(def selects-spec
  {:name 'signed/one-hot-selects :universes []
   :type (function/forall
          [['S val-type] ['k nat]
           ['hs (all-below 'k (fn [i] (sle szero (app 'S i))))]
           ['h01 (all-below 'k (fn [i] (disj* (sequiv (app 'S i) szero) (sequiv (app 'S i) sone))))]
           ['hsum (sequiv (expr-sum-value 'S 'k) sone)]]
          (selected 'S 'k))
   :value
   (function/lam
    [['S val-type] ['k nat]
     ['hs (all-below 'k (fn [i] (sle szero (app 'S i))))]
     ['h01 (all-below 'k (fn [i] (disj* (sequiv (app 'S i) szero) (sequiv (app 'S i) sone))))]
     ['hsum (sequiv (expr-sum-value 'S 'k) sone)]]
    (let [sum (expr-sum-value 'S 'k) goal (selected 'S 'k)
          st (app (function/const* 'signed/one-hot-selects-strengthened []) 'S 'k 'hs 'h01)]
      (use-disj (case-zero 'S 'k) (disj* (case-one 'S 'k) (case-many 'S 'k)) goal st
                ;; ~0 and ~1: 1 ~ 0
                (function/lam [['hz (case-zero 'S 'k)]]
                              (explode goal (app (function/const* 'signed/one-not-equivalent-zero [])
                                                 (equiv-trans sone sum szero (equiv-sym sum sone 'hsum)
                                                              (pleft (sequiv sum szero) (function/forall [['X val-type]] (sequiv (expr-sum-value (weighted 'S 'X) 'k) szero)) 'hz)))))
                (function/lam
                 [['hr (disj* (case-one 'S 'k) (case-many 'S 'k))]]
                 (use-disj (case-one 'S 'k) (case-many 'S 'k) goal 'hr
                           (function/lam [['h1 (case-one 'S 'k)]] (pright (sequiv sum sone) goal 'h1))
                           ;; 1 + 1 <= sum ~ 1 = 1 + 0, so 1 <= 0
                           (function/lam
                            [['h2 (case-many 'S 'k)]]
                            (let [le (le-respects two two sum (signed-add sone szero) (equiv-refl two)
                                                  (equiv-trans sum sone (signed-add sone szero) 'hsum (equiv-sym (signed-add sone szero) sone (add-zero-right sone)))
                                                  'h2)]
                              (explode goal (app (function/const* 'signed/one-not-at-most-zero [])
                                                 (app (function/const* 'signed/at-most-add-left-cancel []) sone szero sone le))))))))))})

(def theorem-specs [strengthened-spec selects-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.one-hot-keep rainbow.math.rational.signed.order-cancellation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-one-hot-selects theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.one-hot-selects))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
