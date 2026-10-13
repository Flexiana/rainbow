(ns rainbow.math.lemmas.stochastic-dominance
  "General lemmas: stochastic dominance. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn prefix [c k] (sum c (s/succ k)))

(defn cu [c u] (f/lam [['cu nat]] (mul (at c 'cu) (at u 'cu))))

(defn abel-terms [c u] (f/lam [['at nat]] (mul (prefix c 'at) (sub (at u 'at) (at u (s/succ 'at))))))

(def abel-spec
  (let [c 'c u 'u
        claim (fn [M] (eqv (sum (cu c u) (s/succ M)) (add (sum (abel-terms c u) M) (mul (prefix c M) (at u M)))))]
    (s/spec 'signed/abel-summation [['c family] ['u family] ['M nat]]
            (claim 'M)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['am nat]] (claim 'am))
                   ;; one term: 0 + c0 u0 ~ 0 + (0 + c0) u0
                   (ring (add s/zero (mul (at c s/nz) (at u s/nz))) (add s/zero (mul (add s/zero (at c s/nz)) (at u s/nz))))
                   (f/lam [['aj nat] ['aih (claim 'aj)]]
                          (let [M 'aj M1 (s/succ M) SM (sum (abel-terms c u) M) CM (prefix c M)
                                cM1 (at c M1) uM (at u M) uM1 (at u M1)
                                lhs (add (sum (cu c u) M1) (mul cM1 uM1))
                                mid (add (add SM (mul CM uM)) (mul cM1 uM1))
                                rhs (add (add SM (mul CM (sub uM uM1))) (mul (add CM cM1) uM1))]
                            (trans lhs mid rhs
                                   (s/add-cong (sum (cu c u) M1) (add SM (mul CM uM)) (mul cM1 uM1) (mul cM1 uM1) 'aih (refl (mul cM1 uM1)))
                                   (ring mid rhs))))
                   'M))))

(def nonpos-product-spec
  (let [x 'x y 'y]
    (s/spec 'signed/nonpositive-product-nonnegative [['x signed] ['y signed] ['hx (le x s/zero)] ['hy (le y s/zero)]]
            (le s/zero (mul x y))
            (let [nx (le-resp (neg s/zero) s/zero (neg x) (neg x) (f/const* 'signed/negate-zero []) (refl (neg x)) (call 'signed/at-most-negate x s/zero 'hx))
                  ny (le-resp (neg s/zero) s/zero (neg y) (neg y) (f/const* 'signed/negate-zero []) (refl (neg y)) (call 'signed/at-most-negate y s/zero 'hy))]
              (le-resp (mul (neg x) s/zero) s/zero (mul (neg x) (neg y)) (mul x y)
                       (call 'signed/multiply-zero-right (neg x)) (ring (mul (neg x) (neg y)) (mul x y))
                       (lmono (neg x) s/zero (neg y) nx ny))))))

(def dominance-spec
  (let [a 'a b 'b u 'u q 'q n (s/succ q)
        c (f/lam [['dc nat]] (sub (at a 'dc) (at b 'dc)))
        AU (cu a u) BU (cu b u) CU (cu c u)
        ;; sum (a - b) u ~ sum a u - sum b u
        split (a/chain (sum CU n)
                       [(sum (f/lam [['ds nat]] (sub (at AU 'ds) (at BU 'ds))) n)
                        (a/sum-cong CU (f/lam [['ds nat]] (sub (at AU 'ds) (at BU 'ds))) n 'sa
                                    (fn [i _] (ring (mul (sub (at a i) (at b i)) (at u i)) (sub (mul (at a i) (at u i)) (mul (at b i) (at u i))))))]
                       [(sub (sum AU n) (sum BU n)) (call 'signed/expr-sum-value-subtract AU BU n)])
        ;; C_k ~ F_A(k) - F_B(k) <= 0
        Ck (fn [k hk] (le-resp (sub (prefix a k) (prefix b k)) (prefix c k) (sub (prefix b k) (prefix b k)) s/zero
                               (sym (prefix c k) (sub (prefix a k) (prefix b k)) (call 'signed/expr-sum-value-subtract a b (s/succ k)))
                               (ring (sub (prefix b k) (prefix b k)) s/zero)
                               (call 'signed/add-right-monotone (prefix a k) (prefix b k) (neg (prefix b k)) (at 'hF k hk))))
        terms-nn (a/sum-mono (f/lam [['z0 nat]] s/zero) (abel-terms c u) q 'sb
                             (fn [k hk] (call 'signed/nonpositive-product-nonnegative (prefix c k) (sub (at u k) (at u (s/succ k)))
                                              (Ck k (s/weaken k q hk))
                                              (le-resp (sub (at u k) (at u (s/succ k))) (sub (at u k) (at u (s/succ k))) (sub (at u (s/succ k)) (at u (s/succ k))) s/zero
                                                       (refl (sub (at u k) (at u (s/succ k)))) (ring (sub (at u (s/succ k)) (at u (s/succ k))) s/zero)
                                                       (call 'signed/add-right-monotone (at u k) (at u (s/succ k)) (neg (at u (s/succ k))) (at 'hu k hk))))))
        Cq (a/chain (prefix c q) [(sub (prefix a q) (prefix b q)) (call 'signed/expr-sum-value-subtract a b n)]
                    [(sub one one) (s/add-cong (prefix a q) one (neg (prefix b q)) (neg one) 'hA (a/neg-cong (prefix b q) one 'hB))]
                    [s/zero (ring (sub one one) s/zero)])
        tail0 (trans (mul (prefix c q) (at u q)) (mul s/zero (at u q)) s/zero (mcong (prefix c q) s/zero (at u q) (at u q) Cq (refl (at u q))) (call 'signed/multiply-zero-left (at u q)))
        abel (call 'signed/abel-summation c u q)
        cu-nn (le-resp (sum (f/lam [['z0 nat]] s/zero) q) s/zero (sum (abel-terms c u) q) (sum CU n)
                       (call 'signed/expr-sum-value-zero q)
                       (a/chain (sum (abel-terms c u) q) [(add (sum (abel-terms c u) q) s/zero) (sym (add (sum (abel-terms c u) q) s/zero) (sum (abel-terms c u) q) (call 'signed/add-zero-right (sum (abel-terms c u) q)))]
                                [(add (sum (abel-terms c u) q) (mul (prefix c q) (at u q))) (s/add-cong (sum (abel-terms c u) q) (sum (abel-terms c u) q) s/zero (mul (prefix c q) (at u q)) (refl (sum (abel-terms c u) q)) (sym (mul (prefix c q) (at u q)) s/zero tail0))]
                                [(sum CU n) (sym (sum CU n) (add (sum (abel-terms c u) q) (mul (prefix c q) (at u q))) abel)])
                       terms-nn)]
    (s/spec 'signed/first-order-dominance-expectation
            [['a family] ['b family] ['u family] ['q nat]
             ['hu (s/all-below q #(le (at u %) (at u (s/succ %))))]
             ['hF (s/all-below n #(le (prefix a %) (prefix b %)))]
             ['hA (eqv (sum a n) one)] ['hB (eqv (sum b n) one)]]
            (le (sum BU n) (sum AU n))
            (le-resp (add (sum BU n) s/zero) (sum BU n) (add (sum BU n) (sub (sum AU n) (sum BU n))) (sum AU n)
                     (call 'signed/add-zero-right (sum BU n)) (ring (add (sum BU n) (sub (sum AU n) (sum BU n))) (sum AU n))
                     (call 'signed/add-left-monotone s/zero (sub (sum AU n) (sum BU n)) (sum BU n)
                           (le-resp s/zero s/zero (sum CU n) (sub (sum AU n) (sum BU n)) (refl s/zero) split cu-nn))))))

(defn utility [U x] (f/lam [['ux nat]] (at U (at x 'ux))))

(defn expected [p U x n] (sum (f/lam [['eu nat]] (mul (at p 'eu) (at U (at x 'eu)))) n))

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

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn monotone-premise [U] ['hU (f/forall [['us signed] ['ut signed] ['ust (le 'us 'ut)]] (le (at U 'us) (at U 'ut)))])

(def borrowed-specs [cpm/negate-le-spec])

(def theorem-specs [abel-spec nonpos-product-spec dominance-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      dot-negate/extend-environment
      (support/extend-with-shared :expr-sum-stochastic-dominance theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
