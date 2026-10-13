(ns rainbow.math.lemmas.hhi-bounds
  "General lemmas: hhi bounds. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(def btrue (f/const* 'data/true []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn lt [x y] (call 'signed/less-than x y))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q)) (lmono p s/zero q hp hq)))

(def ofn of-nat/of-nat)

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn picked [I x c] (disj (eqv I s/zero) (pconj (eqv I one) (eqv x c))))

(defn sq [x] (mul x x))

(def positive-spec
  (let [S 'pi-s D (call 'signed/decide-at-most S s/zero) val (fn [c] (sel one s/zero c))
        not-le (f/lam [['pi-le (le S s/zero)]]
                      (call 'signed/one-not-at-most-zero
                            (f/app (f/const* 'equality/substitution [type-level]) bool D btrue
                                   (call 'signed/decide-at-most-true-complete S s/zero 'pi-le)
                                   (f/lam [['ct bool]] (le one (val 'ct))) 'pi-h)))
        nonneg (cases (le s/zero S) (le S s/zero) (le s/zero S) (call 'signed/at-most-total s/zero S)
                      (f/lam [['pi-a (le s/zero S)]] 'pi-a)
                      (f/lam [['pi-b (le S s/zero)]] (call 'proposition/explode (le s/zero S) (f/app not-le 'pi-b))))]
    (s/spec 'signed/positive-indicator-positive [['pi-s signed] ['pi-h (le one (val D))]]
            (lt s/zero S)
            (call 'signed/less-than-intro s/zero S nonneg
                  (f/lam [['pi-e (eqv s/zero S)]] (f/app not-le (a/eq-le S s/zero (sym s/zero S 'pi-e))))))))

(defn nested-eq-ind [p c] (sel s/zero (center/le-ind c p) (call 'signed/decide-at-most p c)))

(def nested-eq-cases-spec
  (let [p 'ne-p c 'ne-c D (call 'signed/decide-at-most p c) L2 (center/le-ind c p)
        val (fn [t] (sel s/zero L2 t))
        goal (fn [t] (picked (val t) p c))
        eqb (fn [t] (f/equality type-level bool D t))]
    (s/spec 'signed/nested-eq-indicator-cases [['ne-p signed] ['ne-c signed]]
            (goal D)
            (f/app (f/const* 'data/Bool.rec [prop-level])
                   (f/lam [['ne-b bool]] (f/forall [['ne-h (eqb 'ne-b)]] (goal 'ne-b)))
                   (f/lam [['ne-h (eqb (f/const* 'data/false []))]]
                          (inl (eqv s/zero s/zero) (pconj (eqv s/zero one) (eqv p c)) (refl s/zero)))
                   (f/lam [['ne-h (eqb btrue)]]
                          (let [pc (call 'signed/decide-at-most-true-sound p c 'ne-h)]
                            (cases (eqv L2 s/zero) (pconj (eqv L2 one) (le c p)) (goal btrue) (call 'signed/le-indicator-cases c p)
                                   (f/lam [['ne-z (eqv L2 s/zero)]] (inl (eqv L2 s/zero) (pconj (eqv L2 one) (eqv p c)) 'ne-z))
                                   (f/lam [['ne-o (pconj (eqv L2 one) (le c p))]]
                                          (inr (eqv L2 s/zero) (pconj (eqv L2 one) (eqv p c))
                                               (conjoin (eqv L2 one) (eqv p c) (pleft (eqv L2 one) (le c p) 'ne-o)
                                                        (anti p c pc (pright (eqv L2 one) (le c p) 'ne-o))))))))
                   D
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn sq-sum [sv n] (sum (f/lam [['sq-i nat]] (sq (at sv 'sq-i))) n))

(def deviation-spec
  (let [sv 'dv-s n 'dv-n H 'dv-h x 'dv-a N (ofn n) sj #(at sv %)
        T (f/lam [['dj nat]] (mul (sub x (sj 'dj)) (sub x (sj 'dj))))
        A (f/lam [['da nat]] (sq x))
        B (f/lam [['db nat]] (sq (sj 'db)))
        C (f/lam [['dc nat]] (mul x (sj 'dc)))
        AB (f/lam [['de nat]] (add (at A 'de) (at B 'de)))
        CC (f/lam [['df nat]] (add (at C 'df) (at C 'df)))
        T2 (f/lam [['dg nat]] (sub (at AB 'dg) (at CC 'dg)))
        SC (a/chain (sum C n)
                    [(mul x (sum sv n)) (sym (mul x (sum sv n)) (sum C n) (call 'signed/expr-sum-value-scale-left sv x n))]
                    [(mul x one) (mcong x x (sum sv n) one (refl x) 'dv-sum)]
                    [x (times-one x)])]
    (s/spec 'signed/square-deviation-sum
            [['dv-s family] ['dv-n nat] ['dv-h signed] ['dv-sum (eqv (sum sv n) one)] ['dv-hh (eqv H (sq-sum sv n))] ['dv-a signed]]
            (eqv (sum T n) (sub (add (mul (sq x) N) H) (add x x)))
            (a/chain (sum T n)
                     [(sum T2 n) (a/sum-cong T T2 n 'dv-c (fn [j _] (ring (mul (sub x (sj j)) (sub x (sj j))) (sub (add (sq x) (sq (sj j))) (add (mul x (sj j)) (mul x (sj j)))))))]
                     [(sub (sum AB n) (sum CC n)) (call 'signed/expr-sum-value-subtract AB CC n)]
                     [(sub (add (sum A n) (sum B n)) (add (sum C n) (sum C n)))
                      (s/add-cong (sum AB n) (add (sum A n) (sum B n)) (neg (sum CC n)) (neg (add (sum C n) (sum C n)))
                                  (call 'signed/expr-sum-value-add A B n)
                                  (a/neg-cong (sum CC n) (add (sum C n) (sum C n)) (call 'signed/expr-sum-value-add C C n)))]
                     [(sub (add (mul (sq x) N) H) (add x x))
                      (s/add-cong (add (sum A n) (sum B n)) (add (mul (sq x) N) H) (neg (add (sum C n) (sum C n))) (neg (add x x))
                                  (s/add-cong (sum A n) (mul (sq x) N) (sum B n) H (call 'signed/expr-sum-constant-of-nat (sq x) n) (sym H (sum B n) 'dv-hh))
                                  (a/neg-cong (add (sum C n) (sum C n)) (add x x) (s/add-cong (sum C n) x (sum C n) x SC SC)))]))))

(def reciprocal-spec
  (let [sv 'rc-s n 'rc-n H 'rc-h N (ofn n) si #(at sv %)
        row (fn [i] (sum (f/lam [['rj nat]] (mul (sub (si i) (si 'rj)) (sub (si i) (si 'rj)))) n))
        R (f/lam [['ri nat]] (row 'ri))
        R2 (f/lam [['rk nat]] (sub (add (mul (sq (si 'rk)) N) H) (add (si 'rk) (si 'rk))))
        P (f/lam [['rp nat]] (add (mul (sq (si 'rp)) N) H))
        Q (f/lam [['rq nat]] (add (si 'rq) (si 'rq)))
        PA (f/lam [['ra nat]] (mul (sq (si 'ra)) N))
        PB (f/lam [['rb nat]] H)
        HN (mul H N)
        total (a/chain (sum R n)
                       [(sum R2 n) (a/sum-cong R R2 n 'rc-c (fn [i _] (call 'signed/square-deviation-sum sv n H 'rc-sum 'rc-hh (si i))))]
                       [(sub (sum P n) (sum Q n)) (call 'signed/expr-sum-value-subtract P Q n)]
                       [(sub (add (sum PA n) (sum PB n)) (add (sum sv n) (sum sv n)))
                        (s/add-cong (sum P n) (add (sum PA n) (sum PB n)) (neg (sum Q n)) (neg (add (sum sv n) (sum sv n)))
                                    (call 'signed/expr-sum-value-add PA PB n)
                                    (a/neg-cong (sum Q n) (add (sum sv n) (sum sv n)) (call 'signed/expr-sum-value-add sv sv n)))]
                       [(sub (add HN HN) (add one one))
                        (s/add-cong (add (sum PA n) (sum PB n)) (add HN HN) (neg (add (sum sv n) (sum sv n))) (neg (add one one))
                                    (s/add-cong (sum PA n) HN (sum PB n) HN
                                                (a/chain (sum PA n)
                                                         [(mul (sq-sum sv n) N) (sym (mul (sq-sum sv n) N) (sum PA n) (call 'signed/expr-sum-value-scale-right (f/lam [['sq-i nat]] (sq (si 'sq-i))) N n))]
                                                         [HN (mcong (sq-sum sv n) H N N (sym H (sq-sum sv n) 'rc-hh) (refl N))])
                                                (call 'signed/expr-sum-constant-of-nat H n))
                                    (a/neg-cong (add (sum sv n) (sum sv n)) (add one one) (s/add-cong (sum sv n) one (sum sv n) one 'rc-sum 'rc-sum)))])
        nonneg (call 'signed/expr-sum-value-nonnegative R n
                     (f/lam [['rn-i nat] ['rn-h (below 'rn-i n)]]
                            (call 'signed/expr-sum-value-nonnegative (f/lam [['rj nat]] (mul (sub (si 'rn-i) (si 'rj)) (sub (si 'rn-i) (si 'rj)))) n
                                  (f/lam [['rm-j nat] ['rm-h (below 'rm-j n)]]
                                         (let [d (sub (si 'rn-i) (si 'rm-j))]
                                           (call 'signed/zero-at-most-of-nonnegative (mul d d) (call 'signed/square-nonnegative d)))))))
        gap (le-resp s/zero s/zero (sum R n) (sub (add HN HN) (add one one)) (refl s/zero) total nonneg)
        twice (le-resp (add s/zero (add one one)) (add one one) (add (sub (add HN HN) (add one one)) (add one one)) (add HN HN)
                       (ring (add s/zero (add one one)) (add one one)) (ring (add (sub (add HN HN) (add one one)) (add one one)) (add HN HN))
                       (call 'signed/add-right-monotone s/zero (sub (add HN HN) (add one one)) (add one one) gap))]
    (s/spec 'signed/hhi-reciprocal-bound
            [['rc-s family] ['rc-n nat] ['rc-h signed] ['rc-sum (eqv (sum sv n) one)] ['rc-hh (eqv H (sq-sum sv n))]]
            (le one (mul N H))
            (le-resp one one HN (mul N H) (refl one) (call 'signed/multiply-commutative H N)
                     (call 'signed/at-most-halve one HN twice)))))

(defn bounds-prop [H m n]
  (pconj (le (sq m) H) (pconj (le H m) (pconj (le m one) (pconj (le H one) (le one (mul (ofn n) H)))))))

(defn share-binders [sv n H m]
  [['hs (s/all-below n #(le s/zero (at sv %)))]
   ['hsum (eqv (sum sv n) one)]
   ['hh (eqv H (sq-sum sv n))]
   ['hm (s/all-below n #(le (at sv %) m))]
   ['hatt (le one (sum (f/lam [['at-i nat]] (nested-eq-ind (at sv 'at-i) m)) n))]])

(def bounds-spec
  (let [sv 'bd-s n 'bd-n H 'bd-h m 'bd-m si #(at sv %) N (ofn n)
        I (f/lam [['at-i nat]] (nested-eq-ind (si 'at-i) m))
        pick (fn [i] (call 'signed/nested-eq-indicator-cases (si i) m))
        ;; s_i ~ m -> s_i s_i ~ m m
        pick-sq (fn [i hi]
                  (let [Ii (at I i)]
                    (cases (eqv Ii s/zero) (pconj (eqv Ii one) (eqv (si i) m)) (picked Ii (sq (si i)) (sq m)) (pick i)
                           (f/lam [['ps-z (eqv Ii s/zero)]] (inl (eqv Ii s/zero) (pconj (eqv Ii one) (eqv (sq (si i)) (sq m))) 'ps-z))
                           (f/lam [['ps-o (pconj (eqv Ii one) (eqv (si i) m))]]
                                  (let [e (pright (eqv Ii one) (eqv (si i) m) 'ps-o)]
                                    (inr (eqv Ii s/zero) (pconj (eqv Ii one) (eqv (sq (si i)) (sq m)))
                                         (conjoin (eqv Ii one) (eqv (sq (si i)) (sq m)) (pleft (eqv Ii one) (eqv (si i) m) 'ps-o)
                                                  (mcong (si i) m (si i) m e e))))))))
        SQ (f/lam [['sq-i nat]] (sq (si 'sq-i)))
        sq-nn (f/lam [['sn-i nat] ['sn-h (below 'sn-i n)]] (nonneg-prod (si 'sn-i) (si 'sn-i) (at 'hs 'sn-i 'sn-h) (at 'hs 'sn-i 'sn-h)))
        ;; each s_i <= sum s ~ 1, each s_i^2 <= sum s^2 ~ H
        s-le-one (f/lam [['sl-i nat] ['sl-h (below 'sl-i n)]]
                        (le-resp (si 'sl-i) (si 'sl-i) (sum sv n) one (refl (si 'sl-i)) 'hsum
                                 (call 'signed/expr-sum-value-term-bound sv n 'hs 'sl-i 'sl-h)))
        sq-le-H (f/lam [['sh-i nat] ['sh-h (below 'sh-i n)]]
                       (le-resp (sq (si 'sh-i)) (sq (si 'sh-i)) (sum SQ n) H (refl (sq (si 'sh-i))) (sym H (sum SQ n) 'hh)
                                (call 'signed/expr-sum-value-term-bound SQ n sq-nn 'sh-i 'sh-h)))
        m-le-one (call 'signed/indicator-attained-bound I sv m one n (f/lam [['pk-i nat] ['pk-h (below 'pk-i n)]] (pick 'pk-i)) 'hatt s-le-one)
        m2-le-H (call 'signed/indicator-attained-bound I SQ (sq m) H n (f/lam [['pq-i nat] ['pq-h (below 'pq-i n)]] (pick-sq 'pq-i 'pq-h)) 'hatt sq-le-H)
        ;; H ~ sum s_i s_i <= sum m s_i ~ m sum s ~ m
        MS (f/lam [['ms-i nat]] (mul m (si 'ms-i)))
        H-le-m (le-resp (sum SQ n) H (sum MS n) m (sym H (sum SQ n) 'hh)
                        (a/chain (sum MS n) [(mul m (sum sv n)) (sym (mul m (sum sv n)) (sum MS n) (call 'signed/expr-sum-value-scale-left sv m n))]
                                 [(mul m one) (mcong m m (sum sv n) one (refl m) 'hsum)] [m (times-one m)])
                        (a/sum-mono SQ MS n 'bd-c (fn [i hi] (rmono (si i) (si i) m (at 'hs i hi) (at 'hm i hi)))))
        H-le-one (le-trans H m one H-le-m m-le-one)
        recip (call 'signed/hhi-reciprocal-bound sv n H 'hsum 'hh)]
    (s/spec 'signed/hhi-bounds (into [['bd-s family] ['bd-n nat] ['bd-h signed] ['bd-m signed]] (share-binders sv n H m))
            (bounds-prop H m n)
            (conjoin (le (sq m) H) (pconj (le H m) (pconj (le m one) (pconj (le H one) (le one (mul N H)))))
                     m2-le-H
                     (conjoin (le H m) (pconj (le m one) (pconj (le H one) (le one (mul N H))))
                              H-le-m
                              (conjoin (le m one) (pconj (le H one) (le one (mul N H)))
                                       m-le-one
                                       (conjoin (le H one) (le one (mul N H)) H-le-one recip)))))))

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

(def theorem-specs [positive-spec nested-eq-cases-spec deviation-spec reciprocal-spec bounds-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      dot-negate/extend-environment
      norm-nn/extend-environment
      two-terms/extend-environment
      (support/extend-with-shared :expr-sum-hhi-bounds theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
