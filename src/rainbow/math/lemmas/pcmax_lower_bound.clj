(ns rainbow.math.lemmas.pcmax-lower-bound
  "General lemmas: pcmax lower bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
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

(defn lt [x y] (call 'signed/less-than x y))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn load [Y p n i] (sum (f/lam [['lj nat]] (mul (at Y i 'lj) (at p 'lj))) n))

(defn column [Y m j] (sum (f/lam [['ci nat]] (at Y 'ci j)) m))

(defn competitor-binders [Y p Cp m n]
  [['hY01 (all2 'yi m 'yj n #(zero-one (at Y %1 %2)))]
   ['hcol (s/all-below n #(eqv (column Y m %) one))]
   ['hload (s/all-below m #(le (load Y p n %) Cp))]])

(defn y-lo [Y i j hi hj] (call 'signed/zero-one-nonnegative (at Y i j) (at 'hY01 i hi j hj)))

(defn spread [Y p m j hj]
  (let [F (f/lam [['sf nat]] (at Y 'sf j))]
    (a/chain (at p j)
             [(mul one (at p j)) (sym (mul one (at p j)) (at p j) (one-times (at p j)))]
             [(mul (column Y m j) (at p j)) (mcong one (column Y m j) (at p j) (at p j) (sym (column Y m j) one (at 'hcol j hj)) (refl (at p j)))]
             [(sum (f/lam [['sg nat]] (mul (at Y 'sg j) (at p j))) m) (call 'signed/expr-sum-value-scale-right F (at p j) m)])))

(def job-bound-spec
  (let [Y 'Y p 'p m 'm n 'n Cp 'Cp j 'j
        Fj (f/lam [['jf nat]] (mul (at Y 'jf j) (at p j)))
        Gj (f/lam [['jg nat]] (mul (at Y 'jg j) (load Y p n 'jg)))
        Hj (f/lam [['jh nat]] (mul (at Y 'jh j) Cp))
        per-i (fn [i hi]
                ;; Y p_j <= Y L_i: Y ~ 0 makes both 0; Y ~ 1 turns Y L_i into L_i >= Y p_j
                (let [y (at Y i j) Li (load Y p n i) goal (le (mul y (at p j)) (mul y Li))
                      term (call 'signed/expr-sum-value-term-bound (f/lam [['tk nat]] (mul (at Y i 'tk) (at p 'tk))) n
                                 (f/lam [['tn nat] ['tn-lt (below 'tn n)]] (nonneg-prod (at Y i 'tn) (at p 'tn) (y-lo Y i 'tn hi 'tn-lt) (at 'hp 'tn 'tn-lt)))
                                 j 'j-lt)]
                  (cases (eqv y s/zero) (eqv (sub one y) s/zero) goal
                         (call 'signed/multiply-zero-split y (sub one y) (at 'hY01 i hi j 'j-lt))
                         (f/lam [['yz (eqv y s/zero)]]
                                (a/eq-le (mul y (at p j)) (mul y Li)
                                         (a/chain (mul y (at p j))
                                                  [(mul s/zero (at p j)) (mcong y s/zero (at p j) (at p j) 'yz (refl (at p j)))]
                                                  [s/zero (call 'signed/multiply-zero-left (at p j))]
                                                  [(mul s/zero Li) (sym (mul s/zero Li) s/zero (call 'signed/multiply-zero-left Li))]
                                                  [(mul y Li) (mcong s/zero y Li Li (sym y s/zero 'yz) (refl Li))])))
                         (f/lam [['y1 (eqv (sub one y) s/zero)]]
                                (let [yo (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
                                                  [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero 'y1))]
                                                  [one (ring (sub one s/zero) one)])]
                                  (le-resp (mul y (at p j)) (mul y (at p j)) Li (mul y Li) (refl (mul y (at p j)))
                                           (a/chain Li [(mul one Li) (sym (mul one Li) Li (one-times Li))]
                                                    [(mul y Li) (mcong one y Li Li (sym y one yo) (refl Li))])
                                           term))))))]
    (s/spec 'signed/pcmax-job-bound
            (into [['Y matrix] ['p family] ['Cp signed] ['m nat] ['n nat]]
                  (into (competitor-binders Y p Cp m n)
                        [['hp (s/all-below n #(le s/zero (at p %)))] ['j nat] ['j-lt (below 'j n)]]))
            (le (at p j) Cp)
            (le-resp (sum Fj m) (at p j) (sum Hj m) Cp
                     (sym (at p j) (sum Fj m) (spread Y p m j 'j-lt))
                     (a/chain (sum Hj m)
                              [(mul (column Y m j) Cp) (sym (mul (column Y m j) Cp) (sum Hj m) (call 'signed/expr-sum-value-scale-right (f/lam [['sh nat]] (at Y 'sh j)) Cp m))]
                              [(mul one Cp) (mcong (column Y m j) one Cp Cp (at 'hcol j 'j-lt) (refl Cp))]
                              [Cp (one-times Cp)])
                     (le-trans (sum Fj m) (sum Gj m) (sum Hj m)
                               (a/sum-mono Fj Gj m 'jm (fn [i hi] (per-i i hi)))
                               (a/sum-mono Gj Hj m 'jn (fn [i hi] (lmono (at Y i j) (load Y p n i) Cp (y-lo Y i j hi 'j-lt) (at 'hload i hi)))))))))

(def average-bound-spec
  (let [Y 'Y p 'p m 'm n 'n Cp 'Cp
        P (f/lam [['ap nat]] (at p 'ap))
        byjob (f/lam [['aj nat]] (sum (f/lam [['ai nat]] (mul (at Y 'ai 'aj) (at p 'aj))) m))
        bymachine (f/lam [['am nat]] (sum (f/lam [['ak nat]] (mul (at Y 'am 'ak) (at p 'ak))) n))
        swapF (f/lam [['sj nat] ['si nat]] (mul (at Y 'si 'sj) (at p 'sj)))
        C (f/lam [['ac nat]] Cp)]
    (s/spec 'signed/pcmax-average-bound
            (into [['Y matrix] ['p family] ['Cp signed] ['m nat] ['n nat]] (competitor-binders Y p Cp m n))
            (le (sum P n) (mul Cp (of-nat/of-nat m)))
            (le-resp (sum bymachine m) (sum P n) (sum C m) (mul Cp (of-nat/of-nat m))
                     (a/chain (sum bymachine m)
                              [(sum byjob n) (sym (sum byjob n) (sum bymachine m) (call 'signed/expr-sum-value-swap swapF m n))]
                              [(sum P n) (a/sum-cong byjob P n 'aq (fn [j hj] (sym (at p j) (sum (f/lam [['ai nat]] (mul (at Y 'ai j) (at p j))) m) (spread Y p m j hj))))])
                     (call 'signed/expr-sum-constant-of-nat Cp m)
                     (a/sum-mono bymachine C m 'ab (fn [i hi] (at 'hload i hi)))))))

(def cancel-order-spec
  (s/spec 'signed/at-most-cancel-positive-right [['a signed] ['b signed] ['d signed] ['hd (lt s/zero 'd)] ['h (le (mul 'a 'd) (mul 'b 'd))]]
          (le 'a 'b)
          (cases (le 'a 'b) (le 'b 'a) (le 'a 'b) (call 'signed/at-most-total 'a 'b)
                 (f/lam [['ab (le 'a 'b)]] 'ab)
                 (f/lam [['ba (le 'b 'a)]]
                        (let [d0 (call 'signed/less-than-implies-at-most s/zero 'd 'hd)
                              same (call 'signed/at-most-antisymmetric (mul 'a 'd) (mul 'b 'd) 'h (rmono 'd 'b 'a d0 'ba))]
                          (a/eq-le 'a 'b (call 'signed/multiply-cancel-positive-right 'a 'b 'd 'hd same)))))))

(defn m [] (s/succ 'mm))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec indep/total-spec mmck/cancel-or-zero-spec mmck/cancel-positive-spec mmck/successor-positive-spec])

(def theorem-specs [job-bound-spec average-bound-spec cancel-order-spec])

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
      two-terms/extend-environment
      of-nat/extend-environment
      (support/extend-with-shared :expr-sum-pcmax-lower-bound theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
