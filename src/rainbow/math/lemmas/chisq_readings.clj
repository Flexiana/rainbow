(ns rainbow.math.lemmas.chisq-readings
  "General lemmas: chisq readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.linear.vector.norm-nonnegative :as square-nn]
            [rainbow.math.rational.signed.square-zero :as square-zero]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (s/add-cong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn sqnn [x] (call 'signed/zero-at-most-of-nonnegative (mul x x) (call 'signed/square-nonnegative x)))

(defn all-below-as [v n pred] (f/forall [[v nat] [(symbol (str v "-h")) (below v n)]] (pred v)))

(def two-square-sum-spec
  (let [F 'ts-f G 'ts-g n 'ts-n sq (fn [x] (mul x x))
        Q (f/lam [['ts-j nat]] (add (sq (at F 'ts-j)) (sq (at G 'ts-j))))
        term-nn (fn [k] (le-resp (add s/zero s/zero) s/zero (add (sq (at F k)) (sq (at G k))) (add (sq (at F k)) (sq (at G k)))
                                 (ring (add s/zero s/zero) s/zero) (refl (add (sq (at F k)) (sq (at G k))))
                                 (le-trans (add s/zero s/zero) (add (sq (at F k)) s/zero) (add (sq (at F k)) (sq (at G k)))
                                           (call 'signed/add-right-monotone s/zero (sq (at F k)) s/zero (sqnn (at F k)))
                                           (le-resp (add s/zero (sq (at F k))) (add (sq (at F k)) s/zero) (add (sq (at G k)) (sq (at F k))) (add (sq (at F k)) (sq (at G k)))
                                                    (ring (add s/zero (sq (at F k))) (add (sq (at F k)) s/zero)) (ring (add (sq (at G k)) (sq (at F k))) (add (sq (at F k)) (sq (at G k))))
                                                    (call 'signed/add-right-monotone s/zero (sq (at G k)) (sq (at F k)) (sqnn (at G k)))))))
        q-nn (f/lam [['ts-k nat] ['ts-kh (below 'ts-k n)]] (term-nn 'ts-k))
        S0 (anti (sum Q n) s/zero 'ts-h (call 'signed/expr-sum-value-nonnegative Q n q-nn))
        each (at (call 'signed/expr-sum-value-nonnegative-terms-zero Q n) q-nn S0)
        ;; x^2 <= x^2 + y^2 ~ 0 with 0 <= x^2
        one-zero (fn [x y t0]
                   (call 'signed/square-zero-reflects x
                         (anti (sq x) s/zero
                               (le-trans (sq x) (add (sq x) (sq y)) s/zero
                                         (le-resp (add (sq x) s/zero) (sq x) (add (sq x) (sq y)) (add (sq x) (sq y)) (ring (add (sq x) s/zero) (sq x)) (refl (add (sq x) (sq y)))
                                                  (le-resp (add s/zero (sq x)) (add (sq x) s/zero) (add (sq y) (sq x)) (add (sq x) (sq y))
                                                           (ring (add s/zero (sq x)) (add (sq x) s/zero)) (ring (add (sq y) (sq x)) (add (sq x) (sq y)))
                                                           (call 'signed/add-right-monotone s/zero (sq y) (sq x) (sqnn y))))
                                         (a/eq-le (add (sq x) (sq y)) s/zero t0))
                               (sqnn x))))]
    (s/spec 'signed/two-square-sum-zero-terms [['ts-f family] ['ts-g family] ['ts-n nat] ['ts-h (le (sum Q n) s/zero)]]
            (s/all-below n (fn [j] (pconj (eqv (at F j) s/zero) (eqv (at G j) s/zero))))
            (f/lam [['ts-i nat] ['ts-ih (below 'ts-i n)]]
                   (let [x (at F 'ts-i) y (at G 'ts-i) t0 (at each 'ts-i 'ts-ih)]
                     (conjoin (eqv x s/zero) (eqv y s/zero)
                              (one-zero x y t0)
                              (one-zero y x (trans (add (sq y) (sq x)) (add (sq x) (sq y)) s/zero (ring (add (sq y) (sq x)) (add (sq x) (sq y))) t0))))))))

(def eq-of-diff-spec
  (s/spec 'signed/eq-of-difference-zero [['ed-a signed] ['ed-b signed] ['ed-h (eqv (sub 'ed-b 'ed-a) s/zero)]]
          (eqv 'ed-a 'ed-b)
          (from-diff 'ed-a 'ed-b 'ed-h)))

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

(def theorem-specs [two-square-sum-spec eq-of-diff-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      square-nn/extend-environment
      square-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-chisq-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
