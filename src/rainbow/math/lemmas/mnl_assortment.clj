(ns rainbow.math.lemmas.mnl-assortment
  "General lemmas: mnl assortment. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

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

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn one-of [y h]
  (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
           [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero h))]
           [one (ring (sub one s/zero) one)]))

(defn r-one-plus [R S]
  (trans (mul R (add one S)) (add (mul R one) (mul R S)) (add R (mul R S))
         (call 'signed/multiply-distributes-add-left R one S)
         (s/add-cong (mul R one) R (mul R S) (mul R S)
                     (trans (mul R one) (mul one R) R (call 'signed/multiply-commutative R one) (one-times R)) (refl (mul R S)))))

(defn zero-mul-left [x y h] ; x ~ 0  ->  x y ~ 0
  (trans (mul x y) (mul s/zero y) s/zero (mcong x s/zero y y h (refl y)) (call 'signed/multiply-zero-left y)))

(defn nonpos-mul-right [x y hx hy] ; x <= 0, 0 <= y  ->  x y <= 0
  (le-resp (mul x y) (mul x y) (mul s/zero y) s/zero (refl (mul x y)) (call 'signed/multiply-zero-left y) (rmono y x s/zero hy hx)))

(def term-spec
  (let [r 'r v 'v sv 's t 't R 'R g (sub r R) X (mul g v) goal (le (mul (mul t g) v) (mul (mul sv g) v))
        t-lo (call 'signed/zero-one-nonnegative t 'ht)
        t-hi (call 'signed/zero-one-at-most-one t 'ht)]
    (s/spec 'signed/mnl-term-bound
            [['r signed] ['v signed] ['s signed] ['t signed] ['R signed]
             ['hv (le s/zero v)] ['hs (zero-one sv)] ['ht (zero-one t)]
             ['hoff (le (mul sv (sub R r)) s/zero)] ['hleft (le (mul (sub one sv) (sub r R)) s/zero)]]
            goal
            (cases (eqv sv s/zero) (eqv (sub one sv) s/zero) goal (call 'signed/multiply-zero-split sv (sub one sv) 'hs)
                   ;; left out: r - R <= 0; the right side is 0, the left side <= 0
                   (f/lam [['s0 (eqv sv s/zero)]]
                          (let [g-np (le-resp (mul (sub one sv) g) g s/zero s/zero
                                              (a/chain (mul (sub one sv) g)
                                                       [(mul (sub one s/zero) g) (mcong (sub one sv) (sub one s/zero) g g (s/add-cong one one (neg sv) (neg s/zero) (refl one) (a/neg-cong sv s/zero 's0)) (refl g))]
                                                       [(mul one g) (mcong (sub one s/zero) one g g (ring (sub one s/zero) one) (refl g))]
                                                       [g (one-times g)])
                                              (refl s/zero) 'hleft)
                                tg-np (le-resp (mul t g) (mul t g) (mul t s/zero) s/zero (refl (mul t g)) (call 'signed/multiply-zero-right t) (lmono t g s/zero t-lo g-np))]
                            (le-resp (mul (mul t g) v) (mul (mul t g) v) s/zero (mul (mul sv g) v) (refl (mul (mul t g) v))
                                     (sym (mul (mul sv g) v) s/zero (zero-mul-left (mul sv g) v (zero-mul-left sv g 's0)))
                                     (nonpos-mul-right (mul t g) v tg-np 'hv))))
                   ;; offered: r - R >= 0; the left side (t g) v ~ t X <= X ~ the right side
                   (f/lam [['s1 (eqv (sub one sv) s/zero)]]
                          (let [s-one (one-of sv 's1)
                                Rr-np (le-resp (mul sv (sub R r)) (sub R r) s/zero s/zero
                                               (trans (mul sv (sub R r)) (mul one (sub R r)) (sub R r) (mcong sv one (sub R r) (sub R r) s-one (refl (sub R r))) (one-times (sub R r)))
                                               (refl s/zero) 'hoff)
                                g-nn (le-resp (neg s/zero) s/zero (neg (sub R r)) g (f/const* 'signed/negate-zero []) (ring (neg (sub R r)) g)
                                              (call 'signed/at-most-negate (sub R r) s/zero Rr-np))
                                X-nn (le-resp (mul s/zero v) s/zero X X (call 'signed/multiply-zero-left v) (refl X) (rmono v s/zero g 'hv g-nn))
                                lhs-eq (call 'signed/multiply-associative t g v)
                                rhs-eq (a/chain (mul (mul sv g) v) [(mul (mul one g) v) (mcong (mul sv g) (mul one g) v v (mcong sv one g g s-one (refl g)) (refl v))]
                                                [(mul g v) (mcong (mul one g) g v v (one-times g) (refl v))])]
                            (le-resp (mul t X) (mul (mul t g) v) (mul one X) (mul (mul sv g) v)
                                     (sym (mul (mul t g) v) (mul t X) lhs-eq)
                                     (trans (mul one X) X (mul (mul sv g) v) (one-times X) (sym (mul (mul sv g) v) X rhs-eq))
                                     (rmono X t one X-nn t-hi))))))))

(defn gap-sum [u r v R n] (sum (f/lam [['gs nat]] (mul (mul (at u 'gs) (sub (at r 'gs) R)) (at v 'gs))) n))

(defn weight [u v n] (sum (f/lam [['wu nat]] (mul (at u 'wu) (at v 'wu))) n))

(defn revenue [u r v n] (sum (f/lam [['ru nat]] (mul (mul (at u 'ru) (at r 'ru)) (at v 'ru))) n))

(def gap-spec
  (let [u 'u r 'r v 'v R 'R n 'n
        P (f/lam [['p1 nat]] (mul (mul (at u 'p1) (at r 'p1)) (at v 'p1)))
        Q (f/lam [['q1 nat]] (mul R (mul (at u 'q1) (at v 'q1))))
        per (fn [i _]
              (let [ui (at u i) ri (at r i) vi (at v i)]
                (a/chain (mul (mul ui (sub ri R)) vi)
                         [(mul (sub (mul ui ri) (mul ui R)) vi) (mcong (mul ui (sub ri R)) (sub (mul ui ri) (mul ui R)) vi vi (call 'signed/multiply-subtract-expand ui ri R) (refl vi))]
                         [(add (mul (mul ui ri) vi) (mul (neg (mul ui R)) vi)) (call 'signed/multiply-distributes-add-right (mul ui ri) (neg (mul ui R)) vi)]
                         [(sub (mul (mul ui ri) vi) (mul (mul ui R) vi))
                          (s/add-cong (mul (mul ui ri) vi) (mul (mul ui ri) vi) (mul (neg (mul ui R)) vi) (neg (mul (mul ui R) vi)) (refl (mul (mul ui ri) vi))
                                      (call 'signed/multiply-negate-left (mul ui R) vi))]
                         [(sub (mul (mul ui ri) vi) (mul R (mul ui vi)))
                          (s/add-cong (mul (mul ui ri) vi) (mul (mul ui ri) vi) (neg (mul (mul ui R) vi)) (neg (mul R (mul ui vi))) (refl (mul (mul ui ri) vi))
                                      (a/neg-cong (mul (mul ui R) vi) (mul R (mul ui vi))
                                                  (a/chain (mul (mul ui R) vi) [(mul (mul R ui) vi) (mcong (mul ui R) (mul R ui) vi vi (call 'signed/multiply-commutative ui R) (refl vi))]
                                                           [(mul R (mul ui vi)) (call 'signed/multiply-associative R ui vi)])))])))]
    (s/spec 'signed/mnl-weighted-gap [['u family] ['r family] ['v family] ['R signed] ['n nat]]
            (eqv (gap-sum u r v R n) (sub (revenue u r v n) (mul R (weight u v n))))
            (a/chain (gap-sum u r v R n)
                     [(sum (f/lam [['d1 nat]] (sub (at P 'd1) (at Q 'd1))) n)
                      (a/sum-cong (f/lam [['gs nat]] (mul (mul (at u 'gs) (sub (at r 'gs) R)) (at v 'gs))) (f/lam [['d1 nat]] (sub (at P 'd1) (at Q 'd1))) n 'ga per)]
                     [(sub (sum P n) (sum Q n)) (call 'signed/expr-sum-value-subtract P Q n)]
                     [(sub (revenue u r v n) (mul R (weight u v n)))
                      (s/add-cong (sum P n) (revenue u r v n) (neg (sum Q n)) (neg (mul R (weight u v n))) (refl (sum P n))
                                  (a/neg-cong (sum Q n) (mul R (weight u v n))
                                              (sym (mul R (weight u v n)) (sum Q n) (call 'signed/expr-sum-value-scale-left (f/lam [['wu nat]] (mul (at u 'wu) (at v 'wu))) R n))))]))))

(def optimal-spec
  (let [r 'r v 'v sv 's t 't R 'R R2 'R2 n 'n
        S (weight sv v n) T (weight t v n)
        gs (call 'signed/mnl-weighted-gap sv r v R n)
        gt (call 'signed/mnl-weighted-gap t r v R n)
        ;; the accepted gap is R: R (1 + S) - R S
        s-gap (a/chain (gap-sum sv r v R n) [(sub (revenue sv r v n) (mul R S)) gs]
                       [(sub (mul R (add one S)) (mul R S)) (s/add-cong (revenue sv r v n) (mul R (add one S)) (neg (mul R S)) (neg (mul R S)) (sym (mul R (add one S)) (revenue sv r v n) 'hrev) (refl (neg (mul R S))))]
                       [(sub (add R (mul R S)) (mul R S)) (s/add-cong (mul R (add one S)) (add R (mul R S)) (neg (mul R S)) (neg (mul R S)) (r-one-plus R S) (refl (neg (mul R S))))]
                       [R (ring (sub (add R (mul R S)) (mul R S)) R)])
        t-gap (a/chain (gap-sum t r v R n) [(sub (revenue t r v n) (mul R T)) gt]
                       [(sub (mul R2 (add one T)) (mul R T)) (s/add-cong (revenue t r v n) (mul R2 (add one T)) (neg (mul R T)) (neg (mul R T)) (sym (mul R2 (add one T)) (revenue t r v n) 'hrev2) (refl (neg (mul R T))))])
        sum-le (a/sum-mono (f/lam [['gs nat]] (mul (mul (at t 'gs) (sub (at r 'gs) R)) (at v 'gs))) (f/lam [['gs nat]] (mul (mul (at sv 'gs) (sub (at r 'gs) R)) (at v 'gs))) n 'oa
                           (fn [i hi] (call 'signed/mnl-term-bound (at r i) (at v i) (at sv i) (at t i) R (at 'hv i hi) (at 'hs i hi) (at 'ht i hi) (at 'hoff i hi) (at 'hleft i hi))))
        ;; R2 (1 + T) - R T <= R  ->  R2 (1 + T) <= R (1 + T)
        core (le-resp (sub (mul R2 (add one T)) (mul R T)) (sub (mul R2 (add one T)) (mul R T)) (gap-sum sv r v R n) R
                      (refl (sub (mul R2 (add one T)) (mul R T))) s-gap
                      (le-resp (gap-sum t r v R n) (sub (mul R2 (add one T)) (mul R T)) (gap-sum sv r v R n) (gap-sum sv r v R n) t-gap (refl (gap-sum sv r v R n)) sum-le))
        X2 (mul R2 (add one T))
        scaled (le-resp (add (sub X2 (mul R T)) (mul R T)) X2 (add R (mul R T)) (mul R (add one T))
                        (a/chain (add (sub X2 (mul R T)) (mul R T)) [(add (sub (add R2 (mul R2 T)) (mul R T)) (mul R T))
                                                                      (s/add-cong (sub X2 (mul R T)) (sub (add R2 (mul R2 T)) (mul R T)) (mul R T) (mul R T)
                                                                                  (s/add-cong X2 (add R2 (mul R2 T)) (neg (mul R T)) (neg (mul R T)) (r-one-plus R2 T) (refl (neg (mul R T)))) (refl (mul R T)))]
                                 [(add R2 (mul R2 T)) (ring (add (sub (add R2 (mul R2 T)) (mul R T)) (mul R T)) (add R2 (mul R2 T)))]
                                 [X2 (sym X2 (add R2 (mul R2 T)) (r-one-plus R2 T))])
                        (sym (mul R (add one T)) (add R (mul R T)) (r-one-plus R T))
                        (call 'signed/add-right-monotone (sub (mul R2 (add one T)) (mul R T)) R (mul R T) core))
        t-nn (call 'signed/expr-sum-value-nonnegative (f/lam [['wu nat]] (mul (at t 'wu) (at v 'wu))) n
                   (f/lam [['tn nat] ['tn-lt (below 'tn n)]]
                          (le-resp (mul (at t 'tn) s/zero) s/zero (mul (at t 'tn) (at v 'tn)) (mul (at t 'tn) (at v 'tn)) (call 'signed/multiply-zero-right (at t 'tn)) (refl (mul (at t 'tn) (at v 'tn)))
                                   (lmono (at t 'tn) s/zero (at v 'tn) (call 'signed/zero-one-nonnegative (at t 'tn) (at 'ht 'tn 'tn-lt)) (at 'hv 'tn 'tn-lt)))))
        pos (call 'signed/less-than-of-less-than-of-at-most s/zero one (add one T) (f/const* 'signed/zero-less-than-one [])
                  (le-resp (add one s/zero) one (add one T) (add one T) (call 'signed/add-zero-right one) (refl (add one T)) (call 'signed/add-left-monotone s/zero T one t-nn)))]
    (s/spec 'signed/mnl-assortment-optimal
            [['r family] ['v family] ['s family] ['t family] ['R signed] ['R2 signed] ['n nat]
             ['hv (s/all-below n #(le s/zero (at v %)))] ['hs (s/all-below n #(zero-one (at sv %)))]
             ['hrev (eqv (mul R (add one S)) (revenue sv r v n))]
             ['hoff (s/all-below n #(le (mul (at sv %) (sub R (at r %))) s/zero))]
             ['hleft (s/all-below n #(le (mul (sub one (at sv %)) (sub (at r %) R)) s/zero))]
             ['ht (s/all-below n #(zero-one (at t %)))] ['hrev2 (eqv (mul R2 (add one T)) (revenue t r v n))]]
            (le R2 R)
            (call 'signed/at-most-cancel-positive-right R2 R (add one T) pos scaled))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec indep/zero-one-upper-spec indep/subtract-expand-spec indep/total-spec
                     mmck/cancel-or-zero-spec mmck/cancel-positive-spec pcmax/cancel-order-spec cpm/negate-le-spec])

(def theorem-specs [term-spec gap-spec optimal-spec])

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
      dot-negate/extend-environment
      (support/extend-with-shared :expr-sum-mnl-assortment theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
