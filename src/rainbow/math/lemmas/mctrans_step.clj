(ns rainbow.math.lemmas.mctrans-step
  "General lemmas: mctrans step. The mathematical facts the corresponding checks rest on,
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
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn sqnn [x] (call 'signed/zero-at-most-of-nonnegative (mul x x) (call 'signed/square-nonnegative x)))

(defn one-right [r] (trans (mul r one) (mul one r) r (call 'signed/multiply-commutative r one) (call 'signed/multiply-one-left r)))

(def square-sum-spec
  (let [F 'sq-f n 'sq-n Q (f/lam [['sq-j nat]] (mul (at F 'sq-j) (at F 'sq-j)))
        q-nn (f/lam [['sq-k nat] ['sq-kh (below 'sq-k n)]] (sqnn (at F 'sq-k)))
        S0 (anti (sum Q n) s/zero 'sq-h (call 'signed/expr-sum-value-nonnegative Q n q-nn))
        each (at (call 'signed/expr-sum-value-nonnegative-terms-zero Q n) q-nn S0)]
    (s/spec 'signed/square-sum-zero-terms [['sq-f family] ['sq-n nat] ['sq-h (le (sum Q n) s/zero)]]
            (s/all-below n (fn [j] (eqv (at F j) s/zero)))
            (f/lam [['sq-i nat] ['sq-ih (below 'sq-i n)]]
                   (call 'signed/square-zero-reflects (at F 'sq-i) (at each 'sq-i 'sq-ih))))))

(defn all-below-as [v n pred] (f/forall [[v nat] [(symbol (str v "-h")) (below v n)]] (pred v)))

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

(def theorem-specs [square-sum-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      square-nn/extend-environment
      square-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-mctrans-step theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
