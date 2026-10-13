(ns rainbow.math.lemmas.headway-wait
  "General lemmas: headway wait. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn assoc3 [x y z] (call 'signed/multiply-associative x y z))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(defn sq [x] (mul x x))

(def ofn of-nat/of-nat)

(def two (ofn (s/succ (s/succ s/nz))))

(def count-positive-spec
  (let [h 'cp-h claim (fn [k] (f/forall [['cp-pos (lt s/zero (sum h k))]] (lt s/zero (ofn k))))]
    (s/spec 'signed/count-positive-of-sum [['cp-h family] ['cp-n nat]]
            (claim 'cp-n)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['cp-k nat]] (claim 'cp-k))
                   (f/lam [['cp-pos (lt s/zero (sum h s/nz))]]
                          (call 'proposition/explode (lt s/zero (ofn s/nz)) (call 'signed/less-than-irreflexive s/zero 'cp-pos)))
                   (f/lam [['cp-m nat] ['cp-ih (claim 'cp-m)] ['cp-pos (lt s/zero (sum h (s/succ 'cp-m)))]]
                          (call 'signed/of-nat-successor-positive 'cp-m))
                   'cp-n))))

(defn sq-sum [h n] (sum (f/lam [['sq-i nat]] (sq (at h 'sq-i))) n))

(def deviation-spec
  (let [h 'dg-h n 'dg-n S1 'dg-s1 S2 'dg-s2 x 'dg-a N (ofn n) hj #(at h %)
        T (f/lam [['dj nat]] (mul (sub x (hj 'dj)) (sub x (hj 'dj))))
        A (f/lam [['da nat]] (sq x))
        B (f/lam [['db nat]] (sq (hj 'db)))
        C (f/lam [['dc nat]] (mul x (hj 'dc)))
        AB (f/lam [['de nat]] (add (at A 'de) (at B 'de)))
        CC (f/lam [['df nat]] (add (at C 'df) (at C 'df)))
        T2 (f/lam [['dgg nat]] (sub (at AB 'dgg) (at CC 'dgg)))
        SC (a/chain (sum C n)
                    [(mul x (sum h n)) (sym (mul x (sum h n)) (sum C n) (call 'signed/expr-sum-value-scale-left h x n))]
                    [(mul x S1) (mcong x x (sum h n) S1 (refl x) (sym S1 (sum h n) 'dg-h1))])]
    (s/spec 'signed/square-deviation-general
            [['dg-h family] ['dg-n nat] ['dg-s1 signed] ['dg-s2 signed]
             ['dg-h1 (eqv S1 (sum h n))] ['dg-h2 (eqv S2 (sq-sum h n))] ['dg-a signed]]
            (eqv (sum T n) (sub (add (mul (sq x) N) S2) (add (mul x S1) (mul x S1))))
            (a/chain (sum T n)
                     [(sum T2 n) (a/sum-cong T T2 n 'dg-c (fn [j _] (ring (mul (sub x (hj j)) (sub x (hj j))) (sub (add (sq x) (sq (hj j))) (add (mul x (hj j)) (mul x (hj j)))))))]
                     [(sub (sum AB n) (sum CC n)) (call 'signed/expr-sum-value-subtract AB CC n)]
                     [(sub (add (sum A n) (sum B n)) (add (sum C n) (sum C n)))
                      (s/add-cong (sum AB n) (add (sum A n) (sum B n)) (neg (sum CC n)) (neg (add (sum C n) (sum C n)))
                                  (call 'signed/expr-sum-value-add A B n)
                                  (a/neg-cong (sum CC n) (add (sum C n) (sum C n)) (call 'signed/expr-sum-value-add C C n)))]
                     [(sub (add (mul (sq x) N) S2) (add (mul x S1) (mul x S1)))
                      (s/add-cong (add (sum A n) (sum B n)) (add (mul (sq x) N) S2) (neg (add (sum C n) (sum C n))) (neg (add (mul x S1) (mul x S1)))
                                  (s/add-cong (sum A n) (mul (sq x) N) (sum B n) S2 (call 'signed/expr-sum-constant-of-nat (sq x) n) (sym S2 (sum B n) 'dg-h2))
                                  (a/neg-cong (add (sum C n) (sum C n)) (add (mul x S1) (mul x S1)) (s/add-cong (sum C n) (mul x S1) (sum C n) (mul x S1) SC SC)))]))))

(def cauchy-schwarz-spec
  (let [h 'cs-h n 'cs-n S1 'cs-s1 S2 'cs-s2 N (ofn n) hi #(at h %)
        row (fn [i] (sum (f/lam [['rj nat]] (mul (sub (hi i) (hi 'rj)) (sub (hi i) (hi 'rj)))) n))
        R (f/lam [['ri nat]] (row 'ri))
        R2 (f/lam [['rk nat]] (sub (add (mul (sq (hi 'rk)) N) S2) (add (mul (hi 'rk) S1) (mul (hi 'rk) S1))))
        P (f/lam [['rp nat]] (add (mul (sq (hi 'rp)) N) S2))
        Q (f/lam [['rq nat]] (add (mul (hi 'rq) S1) (mul (hi 'rq) S1)))
        PA (f/lam [['ra nat]] (mul (sq (hi 'ra)) N))
        PB (f/lam [['rb nat]] S2)
        QA (f/lam [['rc nat]] (mul (hi 'rc) S1))
        SN (mul S2 N) SS (mul S1 S1)
        qa-sum (a/chain (sum QA n)
                        [(mul (sum h n) S1) (sym (mul (sum h n) S1) (sum QA n) (call 'signed/expr-sum-value-scale-right h S1 n))]
                        [SS (mcong (sum h n) S1 S1 S1 (sym S1 (sum h n) 'cs-h1) (refl S1))])
        total (a/chain (sum R n)
                       [(sum R2 n) (a/sum-cong R R2 n 'cs-c (fn [i _] (call 'signed/square-deviation-general h n S1 S2 'cs-h1 'cs-h2 (hi i))))]
                       [(sub (sum P n) (sum Q n)) (call 'signed/expr-sum-value-subtract P Q n)]
                       [(sub (add (sum PA n) (sum PB n)) (add (sum QA n) (sum QA n)))
                        (s/add-cong (sum P n) (add (sum PA n) (sum PB n)) (neg (sum Q n)) (neg (add (sum QA n) (sum QA n)))
                                    (call 'signed/expr-sum-value-add PA PB n)
                                    (a/neg-cong (sum Q n) (add (sum QA n) (sum QA n)) (call 'signed/expr-sum-value-add QA QA n)))]
                       [(sub (add SN SN) (add SS SS))
                        (s/add-cong (add (sum PA n) (sum PB n)) (add SN SN) (neg (add (sum QA n) (sum QA n))) (neg (add SS SS))
                                    (s/add-cong (sum PA n) SN (sum PB n) SN
                                                (a/chain (sum PA n)
                                                         [(mul (sq-sum h n) N) (sym (mul (sq-sum h n) N) (sum PA n) (call 'signed/expr-sum-value-scale-right (f/lam [['sq-i nat]] (sq (hi 'sq-i))) N n))]
                                                         [SN (mcong (sq-sum h n) S2 N N (sym S2 (sq-sum h n) 'cs-h2) (refl N))])
                                                (call 'signed/expr-sum-constant-of-nat S2 n))
                                    (a/neg-cong (add (sum QA n) (sum QA n)) (add SS SS) (s/add-cong (sum QA n) SS (sum QA n) SS qa-sum qa-sum)))])
        nonneg (call 'signed/expr-sum-value-nonnegative R n
                     (f/lam [['cn-i nat] ['cn-h (below 'cn-i n)]]
                            (call 'signed/expr-sum-value-nonnegative (f/lam [['rj nat]] (mul (sub (hi 'cn-i) (hi 'rj)) (sub (hi 'cn-i) (hi 'rj)))) n
                                  (f/lam [['cm-j nat] ['cm-h (below 'cm-j n)]]
                                         (let [d (sub (hi 'cn-i) (hi 'cm-j))]
                                           (call 'signed/zero-at-most-of-nonnegative (mul d d) (call 'signed/square-nonnegative d)))))))
        gap (le-resp s/zero s/zero (sum R n) (sub (add SN SN) (add SS SS)) (refl s/zero) total nonneg)
        twice (le-resp (add s/zero (add SS SS)) (add SS SS) (add (sub (add SN SN) (add SS SS)) (add SS SS)) (add SN SN)
                       (ring (add s/zero (add SS SS)) (add SS SS)) (ring (add (sub (add SN SN) (add SS SS)) (add SS SS)) (add SN SN))
                       (call 'signed/add-right-monotone s/zero (sub (add SN SN) (add SS SS)) (add SS SS) gap))]
    (s/spec 'signed/cauchy-schwarz-sum
            [['cs-h family] ['cs-n nat] ['cs-s1 signed] ['cs-s2 signed] ['cs-h1 (eqv S1 (sum h n))] ['cs-h2 (eqv S2 (sq-sum h n))]]
            (le SS (mul N S2))
            (le-resp SS SS SN (mul N S2) (refl SS) (comm S2 N) (call 'signed/at-most-halve SS SN twice)))))

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

(def theorem-specs [count-positive-spec deviation-spec cauchy-schwarz-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      of-nat/extend-environment
      multiply-associative/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      norm-nn/extend-environment
      (support/extend-with-shared :expr-sum-headway-wait theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
