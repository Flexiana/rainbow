(ns rainbow.math.lemmas.durbin-bounds
  "General lemmas: durbin bounds. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.linear.vector.norm-nonnegative :as square-nn]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn sq [x] (mul x x))

(defn sqnn [x] (call 'signed/zero-at-most-of-nonnegative (mul x x) (call 'signed/square-nonnegative x)))

(defn dbl [x] (add x x))

(defn le-add [x y hy] (le-resp (add x s/zero) x (add x y) (add x y) (ring (add x s/zero) x) (refl (add x y)) (call 'signed/add-left-monotone s/zero y x hy)))

(defn add-le [x x' y y' hx hy] (call 'signed/add-monotone x x' y y' hx hy))

(def term-spec
  (let [[a' b'] '[dw-a dw-b] lhs (sq (sub a' b')) rhs (dbl (add (sq a') (sq b')))]
    (s/spec 'signed/dw-term [['dw-a signed] ['dw-b signed]]
            (le lhs rhs)
            (le-resp lhs lhs (add lhs (sq (add a' b'))) rhs (refl lhs) (ring (add lhs (sq (add a' b'))) rhs)
                     (le-add lhs (sq (add a' b')) (sqnn (add a' b')))))))

(defn fam [h] (f/lam [['df-t nat]] (h 'df-t)))

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

(def theorem-specs [term-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      square-nn/extend-environment
      (support/extend-with-shared :expr-sum-durbin-bounds theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
