(ns rainbow.math.lemmas.vertex-cover-approx
  "General lemmas: vertex cover approx. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn uncovered-term [A c u v] (mul (mul (at A u v) (sub one (at c u))) (sub one (at c v))))

(defn cover-rows [A c n]
  (s/all-below n (fn [u] (le (sum (f/lam [['cv nat]] (uncovered-term A c u 'cv)) n) s/zero))))

(defn out-sum [M n u] (sum (f/lam [['ov nat]] (at M u 'ov)) n))

(defn in-sum [M n u] (sum (f/lam [['iv nat]] (at M 'iv u)) n))

(defn matching-size [M n] (sum (f/lam [['mu nat]] (out-sum M n 'mu)) n))

(defn total [c n] (sum (f/lam [['tu nat]] (at c 'tu)) n))

(defn binders [A M c n]
  [['hA0 (all2 'au n 'av n #(le s/zero (at A %1 %2)))]
   ['hM0 (all2 'mu n 'mv n #(le s/zero (at M %1 %2)))]
   ['hMA (all2 'xu n 'xv n #(le (at M %1 %2) (at A %1 %2)))]
   ['hc01 (s/all-below n #(zero-one (at c %)))]
   ['hcover (cover-rows A c n)]
   ['hdeg (s/all-below n #(le (add (out-sum M n %) (in-sum M n %)) one))]])

(def matching-spec
  (let [A 'A M 'M c 'c n 'n
        cv #(at c %) Mv #(at M %1 %2)
        c-lo (fn [u hu] (call 'signed/zero-one-nonnegative (cv u) (at 'hc01 u hu)))
        c-hi (fn [u hu] (call 'signed/zero-one-at-most-one (cv u) (at 'hc01 u hu)))
        o-lo (fn [u hu] (call 'signed/one-minus-nonnegative (cv u) (c-hi u hu)))
        ;; each uncovered term is zero
        row-zero (fn [u hu]
                   (let [F (f/lam [['rz nat]] (uncovered-term A c u 'rz))
                         terms (f/lam [['rt nat] ['rt-lt (below 'rt n)]]
                                      (nonneg-prod (mul (at A u 'rt) (sub one (cv u))) (sub one (cv 'rt))
                                                   (nonneg-prod (at A u 'rt) (sub one (cv u)) (at 'hA0 u hu 'rt 'rt-lt) (o-lo u hu))
                                                   (o-lo 'rt 'rt-lt)))
                         zero-sum (call 'signed/at-most-antisymmetric (sum F n) s/zero (at 'hcover u hu)
                                        (call 'signed/expr-sum-value-nonnegative F n terms))]
                     (call 'signed/expr-sum-value-nonnegative-terms-zero F n terms zero-sum)))
        ;; M(u,v) <= M c_u + M c_v
        arc (fn [u v hu hv]
              (let [m (Mv u v) mcu (mul m (cv u)) mcv (mul m (cv v))
                    goal (le m (add mcu mcv))
                    mcv0 (nonneg-prod m (cv v) (at 'hM0 u hu v hv) (c-lo v hv))
                    mcu0 (nonneg-prod m (cv u) (at 'hM0 u hu v hv) (c-lo u hu))]
                (cases (eqv (cv u) s/zero) (eqv (sub one (cv u)) s/zero) goal
                       (call 'signed/multiply-zero-split (cv u) (sub one (cv u)) (at 'hc01 u hu))
                       (f/lam [['cz (eqv (cv u) s/zero)]]
                              ;; 1 - c_u ~ 1, so M (1 - c_v) <= adj (1 - c_u) (1 - c_v) ~ 0
                              (let [ou1 (a/chain (sub one (cv u)) [(sub one s/zero) (s/add-cong one one (neg (cv u)) (neg s/zero) (refl one) (a/neg-cong (cv u) s/zero 'cz))]
                                                 [one (ring (sub one s/zero) one)])
                                    ov (sub one (cv v)) A1 (mul (at A u v) (sub one (cv u)))
                                    adj-term (a/chain (uncovered-term A c u v)
                                                      [(mul (mul (at A u v) one) ov) (mcong A1 (mul (at A u v) one) ov ov (mcong (at A u v) (at A u v) (sub one (cv u)) one (refl (at A u v)) ou1) (refl ov))]
                                                      [(mul (at A u v) ov) (mcong (mul (at A u v) one) (at A u v) ov ov (times-one (at A u v)) (refl ov))])
                                    upper (le-resp (mul m ov) (mul m ov) (mul (at A u v) ov) s/zero (refl (mul m ov))
                                                   (trans (mul (at A u v) ov) (uncovered-term A c u v) s/zero
                                                          (sym (uncovered-term A c u v) (mul (at A u v) ov) adj-term) (at (row-zero u hu) v hv))
                                                   (rmono ov m (at A u v) (o-lo v hv) (at 'hMA u hu v hv)))
                                    lower (nonneg-prod m ov (at 'hM0 u hu v hv) (o-lo v hv))
                                    m-ov (call 'signed/at-most-antisymmetric (mul m ov) s/zero upper lower)
                                    ;; m ~ m c_v:  m (1 - c_v) ~ m - m c_v ~ 0
                                    ;; m (1 - c_v) ~ m - m c_v, without ring-normalising a product with one
                                    m-ov-expand (trans (mul m ov) (sub (mul m one) mcv) (sub m mcv)
                                                       (call 'signed/multiply-subtract-expand m one (cv v))
                                                       (s/add-cong (mul m one) m (neg mcv) (neg mcv) (times-one m) (refl (neg mcv))))
                                    m-eq (a/chain m [(add (sub m mcv) mcv) (ring m (add (sub m mcv) mcv))]
                                                  [(add (mul m ov) mcv)
                                                   (s/add-cong (sub m mcv) (mul m ov) mcv mcv (sym (mul m ov) (sub m mcv) m-ov-expand) (refl mcv))]
                                                  [(add s/zero mcv) (s/add-cong (mul m ov) s/zero mcv mcv m-ov (refl mcv))]
                                                  [mcv (ring (add s/zero mcv) mcv)])]
                                (le-trans m mcv (add mcu mcv) (a/eq-le m mcv m-eq)
                                          (le-resp (add s/zero mcv) mcv (add mcu mcv) (add mcu mcv) (ring (add s/zero mcv) mcv) (refl (add mcu mcv))
                                                   (call 'signed/add-right-monotone s/zero mcu mcv mcu0)))))
                       (f/lam [['c1 (eqv (sub one (cv u)) s/zero)]]
                              ;; c_u ~ 1, so M c_u ~ M
                              (let [cu1 (a/chain (cv u) [(sub one (sub one (cv u))) (ring (cv u) (sub one (sub one (cv u))))]
                                                 [(sub one s/zero) (s/add-cong one one (neg (sub one (cv u))) (neg s/zero) (refl one) (a/neg-cong (sub one (cv u)) s/zero 'c1))]
                                                 [one (ring (sub one s/zero) one)])
                                    mcu-m (a/chain mcu [(mul m one) (mcong m m (cv u) one (refl m) cu1)] [m (times-one m)])]
                                (le-trans m mcu (add mcu mcv) (a/eq-le m mcu (sym mcu m mcu-m))
                                          (le-resp (add mcu s/zero) mcu (add mcu mcv) (add mcu mcv) (ring (add mcu s/zero) mcu) (refl (add mcu mcv))
                                                   (call 'signed/add-left-monotone s/zero mcv mcu mcv0))))))))
        ;; sum over arcs
        Rf (fn [u] (f/lam [['r1 nat]] (add (mul (Mv u 'r1) (cv u)) (mul (Mv u 'r1) (cv 'r1)))))
        R1 (fn [u] (f/lam [['r2 nat]] (mul (Mv u 'r2) (cv u))))
        R2 (fn [u] (f/lam [['r3 nat]] (mul (Mv u 'r3) (cv 'r3))))
        outer-R (f/lam [['o1 nat]] (sum (Rf 'o1) n))
        out-part (f/lam [['o2 nat]] (mul (cv 'o2) (out-sum M n 'o2)))
        in-part (f/lam [['o3 nat]] (mul (cv 'o3) (in-sum M n 'o3)))
        first-sum (f/lam [['o4 nat]] (sum (R1 'o4) n))
        second-sum (f/lam [['o5 nat]] (sum (R2 'o5) n))
        step1 (a/sum-mono (f/lam [['s1 nat]] (out-sum M n 's1)) outer-R n 'sm
                          (fn [u hu] (a/sum-mono (f/lam [['ov nat]] (at M u 'ov)) (Rf u) n 'sv (fn [v hv] (arc u v hu hv)))))
        first-eq (a/sum-cong first-sum out-part n 'fe
                             (fn [u _] (a/chain (sum (R1 u) n)
                                                [(mul (out-sum M n u) (cv u)) (sym (mul (out-sum M n u) (cv u)) (sum (R1 u) n)
                                                                                   (call 'signed/expr-sum-value-scale-right (f/lam [['ov nat]] (at M u 'ov)) (cv u) n))]
                                                [(mul (cv u) (out-sum M n u)) (comm (out-sum M n u) (cv u))])))
        swap-F (f/lam [['wu nat] ['wv nat]] (mul (Mv 'wu 'wv) (cv 'wv)))
        by-column (f/lam [['cw nat]] (sum (f/lam [['cr nat]] (mul (Mv 'cr 'cw) (cv 'cw))) n))
        second-eq (a/chain (sum second-sum n)
                           [(sum by-column n) (call 'signed/expr-sum-value-swap swap-F n n)]
                           [(sum in-part n)
                            (a/sum-cong by-column in-part n 'se
                                        (fn [w _] (a/chain (sum (f/lam [['cr nat]] (mul (Mv 'cr w) (cv w))) n)
                                                           [(mul (in-sum M n w) (cv w)) (sym (mul (in-sum M n w) (cv w)) (sum (f/lam [['cr nat]] (mul (Mv 'cr w) (cv w))) n)
                                                                                             (call 'signed/expr-sum-value-scale-right (f/lam [['iv nat]] (at M 'iv w)) (cv w) n))]
                                                           [(mul (cv w) (in-sum M n w)) (comm (in-sum M n w) (cv w))])))])
        split (a/chain (sum outer-R n)
                       [(sum (f/lam [['sp nat]] (add (sum (R1 'sp) n) (sum (R2 'sp) n))) n)
                        (a/sum-cong outer-R (f/lam [['sp nat]] (add (sum (R1 'sp) n) (sum (R2 'sp) n))) n 'sc
                                    (fn [u _] (call 'signed/expr-sum-value-add (R1 u) (R2 u) n)))]
                       [(add (sum first-sum n) (sum second-sum n)) (call 'signed/expr-sum-value-add first-sum second-sum n)]
                       [(add (sum out-part n) (sum in-part n))
                        (s/add-cong (sum first-sum n) (sum out-part n) (sum second-sum n) (sum in-part n) first-eq second-eq)])
        combined (a/chain (add (sum out-part n) (sum in-part n))
                          [(sum (f/lam [['cb nat]] (add (at out-part 'cb) (at in-part 'cb))) n)
                           (sym (sum (f/lam [['cb nat]] (add (at out-part 'cb) (at in-part 'cb))) n) (add (sum out-part n) (sum in-part n))
                                (call 'signed/expr-sum-value-add out-part in-part n))]
                          [(sum (f/lam [['cd nat]] (mul (cv 'cd) (add (out-sum M n 'cd) (in-sum M n 'cd)))) n)
                           (a/sum-cong (f/lam [['cb nat]] (add (at out-part 'cb) (at in-part 'cb))) (f/lam [['cd nat]] (mul (cv 'cd) (add (out-sum M n 'cd) (in-sum M n 'cd)))) n 'ce
                                       (fn [w _] (sym (mul (cv w) (add (out-sum M n w) (in-sum M n w))) (add (mul (cv w) (out-sum M n w)) (mul (cv w) (in-sum M n w)))
                                                      (call 'signed/multiply-distributes-add-left (cv w) (out-sum M n w) (in-sum M n w)))))])
        degree-bound (a/sum-mono (f/lam [['cd nat]] (mul (cv 'cd) (add (out-sum M n 'cd) (in-sum M n 'cd)))) (f/lam [['cf nat]] (at c 'cf)) n 'db
                                 (fn [w hw] (le-resp (mul (cv w) (add (out-sum M n w) (in-sum M n w))) (mul (cv w) (add (out-sum M n w) (in-sum M n w)))
                                                     (mul (cv w) one) (cv w) (refl (mul (cv w) (add (out-sum M n w) (in-sum M n w)))) (times-one (cv w))
                                                     (lmono (cv w) (add (out-sum M n w) (in-sum M n w)) one (c-lo w hw) (at 'hdeg w hw)))))
        rhs (sum (f/lam [['cd nat]] (mul (cv 'cd) (add (out-sum M n 'cd) (in-sum M n 'cd)))) n)]
    (s/spec 'signed/matching-at-most-vertex-cover
            (into [['A matrix] ['M matrix] ['c family] ['n nat]] (binders 'A 'M 'c 'n))
            (le (matching-size M n) (total c n))
            (le-trans (matching-size M n) rhs (total c n)
                      (le-resp (matching-size M n) (matching-size M n) (sum outer-R n) rhs (refl (matching-size M n))
                               (trans (sum outer-R n) (add (sum out-part n) (sum in-part n)) rhs split combined) step1)
                      degree-bound))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec
                     indep/zero-one-upper-spec indep/one-minus-spec indep/subtract-expand-spec mmck/successor-positive-spec])

(def theorem-specs [matching-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-associative/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      (support/extend-with-shared :expr-sum-vertex-cover-approx theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
