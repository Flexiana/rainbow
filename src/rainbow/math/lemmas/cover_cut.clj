(ns rainbow.math.lemmas.cover-cut
  "General lemmas: cover cut. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (trans (mul x one) (mul one x) x (call 'signed/multiply-commutative x one) (one-times x)))

(defn zero-plus [x] (trans (add s/zero x) (add x s/zero) x (call 'signed/add-commutative s/zero x) (call 'signed/add-zero-right x)))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn split [x h] (call 'signed/multiply-zero-split x (sub one x) h))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn one-of [y h]
  (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
           [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero h))]
           [one (ring (sub one s/zero) one)]))

(defn zero-or-one [x] (disj (eqv x s/zero) (eqv x one)))

(def zero-or-at-least-one-spec
  (let [claim (fn [k] (f/forall [['zo-h (s/all-below k #(zero-or-one (at 'F %)))]]
                                (disj (eqv (sum 'F k) s/zero) (le one (sum 'F k)))))
        base (f/lam [['zb-h (s/all-below s/nz #(zero-or-one (at 'F %)))]]
                    (inl (eqv (sum 'F s/nz) s/zero) (le one (sum 'F s/nz)) (refl s/zero)))
        step (let [j 'zj S (sum 'F j) t (at 'F j) St (add S t)
                   L (eqv St s/zero) R (le one St)
                   hj (f/lam [['zi nat] ['zi-lt (below 'zi j)]] (at 'zs-h 'zi (s/weaken 'zi j 'zi-lt)))
                   ht (at 'zs-h j (s/self-below j))
                   t-nn (cases (eqv t s/zero) (eqv t one) (le s/zero t) ht
                               (f/lam [['zt0 (eqv t s/zero)]] (a/eq-le s/zero t (sym t s/zero 'zt0)))
                               (f/lam [['zt1 (eqv t one)]] (le-resp s/zero s/zero one t (refl s/zero) (sym t one 'zt1) zero-le-one)))]
               (f/lam [['zj nat] ['zih (claim 'zj)] ['zs-h (s/all-below (s/succ j) #(zero-or-one (at 'F %)))]]
                      (cases (eqv S s/zero) (le one S) (disj L R) (at 'zih hj)
                             (f/lam [['zs0 (eqv S s/zero)]]
                                    (cases (eqv t s/zero) (eqv t one) (disj L R) ht
                                           (f/lam [['zu0 (eqv t s/zero)]]
                                                  (inl L R (a/chain St [(add s/zero s/zero) (s/add-cong S s/zero t s/zero 'zs0 'zu0)]
                                                                    [s/zero (call 'signed/add-zero-right s/zero)])))
                                           (f/lam [['zu1 (eqv t one)]]
                                                  (inr L R (a/eq-le one St (a/chain one [(add s/zero one) (sym (add s/zero one) one (zero-plus one))]
                                                                                    [St (s/add-cong s/zero S one t (sym S s/zero 'zs0) (sym t one 'zu1))]))))))
                             (f/lam [['zs1 (le one S)]]
                                    (inr L R (le-trans one S St 'zs1
                                                       (le-resp (add S s/zero) S St St (call 'signed/add-zero-right S) (refl St)
                                                                (call 'signed/add-left-monotone s/zero t S t-nn))))))))]
    (s/spec 'signed/expr-sum-value-zero-or-at-least-one [['F family] ['k nat]] (claim 'k)
            (f/app (f/const* 'data/Nat.rec [[:zero]]) (f/lam [['zk nat]] (claim 'zk)) base step 'k))))

(defn AX [a x] (f/lam [['ax nat]] (mul (at a 'ax) (at x 'ax))))

(defn AC [a c] (f/lam [['ac nat]] (mul (at a 'ac) (at c 'ac))))

(defn CX [c x] (f/lam [['cx nat]] (mul (at c 'cx) (at x 'cx))))

(defn CS [c] (f/lam [['cs nat]] (at c 'cs)))

(defn DS [c x] (f/lam [['ds nat]] (mul (at c 'ds) (sub one (at x 'ds)))))

(defn cover-binders [a c x b n]
  [['ha (s/all-below n #(le s/zero (at a %)))]
   ['hc (s/all-below n #(zero-one (at c %)))]
   ['hx (s/all-below n #(zero-one (at x %)))]
   ['hfeas (le (sum (AX a x) n) b)]
   ['hcover (call 'proposition/negation (le (sum (AC a c) n) b))]])

(def cover-valid-spec
  (let [a 'a c 'c x 'x b 'b n 'n
        D (DS c x) SC (sum (CS c) n) SCX (sum (CX c x) n) U (sub SC SCX)
        goal (le SCX (sub SC one))
        dz (fn [j hj]
             (let [cj (at c j) xj (at x j) dj (mul cj (sub one xj)) L (eqv dj s/zero) R (eqv dj one)]
               (cases (eqv cj s/zero) (eqv (sub one cj) s/zero) (disj L R) (split cj (at 'hc j hj))
                      (f/lam [['dc0 (eqv cj s/zero)]]
                             (inl L R (a/chain dj [(mul s/zero (sub one xj)) (mcong cj s/zero (sub one xj) (sub one xj) 'dc0 (refl (sub one xj)))]
                                               [s/zero (call 'signed/multiply-zero-left (sub one xj))])))
                      (f/lam [['dc1 (eqv (sub one cj) s/zero)]]
                             (cases (eqv xj s/zero) (eqv (sub one xj) s/zero) (disj L R) (split xj (at 'hx j hj))
                                    (f/lam [['dx0 (eqv xj s/zero)]]
                                           (inr L R (a/chain dj [(mul one (sub one s/zero))
                                                                 (mcong cj one (sub one xj) (sub one s/zero) (one-of cj 'dc1)
                                                                        (s/add-cong one one (neg xj) (neg s/zero) (refl one) (a/neg-cong xj s/zero 'dx0)))]
                                                             [(sub one s/zero) (one-times (sub one s/zero))]
                                                             [one (ring (sub one s/zero) one)])))
                                    (f/lam [['dx1 (eqv (sub one xj) s/zero)]]
                                           (inl L R (a/chain dj [(mul cj s/zero) (mcong cj cj (sub one xj) s/zero (refl cj) 'dx1)]
                                                             [s/zero (call 'signed/multiply-zero-right cj)]))))))))
        dz-all (f/lam [['dj nat] ['dj-lt (below 'dj n)]] (dz 'dj 'dj-lt))
        d-nn (f/lam [['nj nat] ['nj-lt (below 'nj n)]]
                    (let [dj (at D 'nj)]
                      (cases (eqv dj s/zero) (eqv dj one) (le s/zero dj) (dz 'nj 'nj-lt)
                             (f/lam [['nd0 (eqv dj s/zero)]] (a/eq-le s/zero dj (sym dj s/zero 'nd0)))
                             (f/lam [['nd1 (eqv dj one)]] (le-resp s/zero s/zero one dj (refl s/zero) (sym dj one 'nd1) zero-le-one)))))
        ;; D ~ 0: a.c <= a.x <= b, against the strict cover
        from-zero (fn [hD]
                    (let [tz (call 'signed/expr-sum-value-nonnegative-terms-zero D n d-nn hD)
                          per-j (fn [j hj]
                                  (let [aj (at a j) cj (at c j) xj (at x j)]
                                    (cases (eqv cj s/zero) (eqv (sub one cj) s/zero) (le (mul aj cj) (mul aj xj)) (split cj (at 'hc j hj))
                                           (f/lam [['pc0 (eqv cj s/zero)]]
                                                  (le-resp s/zero (mul aj cj) (mul aj xj) (mul aj xj)
                                                           (sym (mul aj cj) s/zero (a/chain (mul aj cj) [(mul aj s/zero) (mcong aj aj cj s/zero (refl aj) 'pc0)]
                                                                                            [s/zero (call 'signed/multiply-zero-right aj)]))
                                                           (refl (mul aj xj))
                                                           (nonneg-prod aj xj (at 'ha j hj) (call 'signed/zero-one-nonnegative xj (at 'hx j hj)))))
                                           (f/lam [['pc1 (eqv (sub one cj) s/zero)]]
                                                  (let [c1 (one-of cj 'pc1)
                                                        x1' (a/chain (sub one xj) [(mul one (sub one xj)) (sym (mul one (sub one xj)) (sub one xj) (one-times (sub one xj)))]
                                                                     [(mul cj (sub one xj)) (mcong one cj (sub one xj) (sub one xj) (sym cj one c1) (refl (sub one xj)))]
                                                                     [s/zero (at tz j hj)])
                                                        x1 (one-of xj x1')]
                                                    (a/eq-le (mul aj cj) (mul aj xj)
                                                             (a/chain (mul aj cj) [(mul aj one) (mcong aj aj cj one (refl aj) c1)]
                                                                      [(mul aj xj) (mcong aj aj one xj (refl aj) (sym xj one x1))])))))))
                          load-le (le-trans (sum (AC a c) n) (sum (AX a x) n) b (a/sum-mono (AC a c) (AX a x) n 'cm per-j) 'hfeas)]
                      (call 'proposition/explode goal (at 'hcover load-le))))
        ;; D >= 1: sum c - sum c x >= 1
        from-one (fn [hD]
                   (let [G (f/lam [['gj nat]] (sub (at (CS c) 'gj) (at (CX c x) 'gj)))
                         D-sub (a/chain (sum D n)
                                        [(sum G n) (a/sum-cong D G n 'ce
                                                               (fn [j _] (let [cj (at c j) xj (at x j)]
                                                                           (trans (mul cj (sub one xj)) (add (mul cj one) (neg (mul cj xj))) (sub cj (mul cj xj))
                                                                                  (call 'signed/multiply-subtract-expand cj one xj)
                                                                                  (s/add-cong (mul cj one) cj (neg (mul cj xj)) (neg (mul cj xj)) (times-one cj) (refl (neg (mul cj xj))))))))]
                                        [U (call 'signed/expr-sum-value-subtract (CS c) (CX c x) n)])
                         hU (le-resp one one (sum D n) U (refl one) D-sub hD)
                         T SCX]
                     (le-resp (add one (sub T one)) T (add U (sub T one)) (sub SC one)
                              (ring (add one (sub T one)) T) (ring (add U (sub T one)) (sub SC one))
                              (call 'signed/add-right-monotone one U (sub T one) hU))))]
    (s/spec 'signed/cover-inequality-valid
            (into [['a family] ['c family] ['x family] ['b signed] ['n nat]] (cover-binders a c x b n))
            goal
            (cases (eqv (sum D n) s/zero) (le one (sum D n)) goal
                   (call 'signed/expr-sum-value-zero-or-at-least-one D n dz-all)
                   (f/lam [['hD0 (eqv (sum D n) s/zero)]] (from-zero 'hD0))
                   (f/lam [['hD1 (le one (sum D n))]] (from-one 'hD1))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(def borrowed-specs [kmeans/zero-one-nonneg-spec indep/subtract-expand-spec])

(def theorem-specs [zero-or-at-least-one-spec cover-valid-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      dot-negate/extend-environment
      (support/extend-with-shared :expr-sum-cover-cut theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
