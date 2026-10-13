(ns rainbow.math.lemmas.sproj-projection
  "General lemmas: sproj projection. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q)) (lmono p s/zero q hp hq)))

(def term-spec
  (let [[v x t y] '[st-v st-x st-t st-y] mu (sub x (sub v t)) A (mul t (sub y x)) L (mul (sub v x) (sub y x))
        mux0 (a/chain (mul mu x) [(mul x mu) (ring (mul mu x) (mul x mu))] [s/zero 'st-p])
        muy (nn-prod mu y (diff-nn (sub v t) x 'st-1) 'st-y0)]
    (s/spec 'signed/sproj-term
            [['st-v signed] ['st-x signed] ['st-t signed] ['st-y signed]
             ['st-1 (le (sub v t) x)] ['st-p (eqv (mul x mu) s/zero)] ['st-y0 (le s/zero y)]]
            (le L A)
            (le-resp (sub A (mul mu y)) L (add A (neg s/zero)) A
                     (a/chain (sub A (mul mu y))
                              [(add (sub A (mul mu y)) s/zero) (ring (sub A (mul mu y)) (add (sub A (mul mu y)) s/zero))]
                              [(add (sub A (mul mu y)) (mul mu x)) (acong (sub A (mul mu y)) (sub A (mul mu y)) s/zero (mul mu x)
                                                                          (refl (sub A (mul mu y))) (sym (mul mu x) s/zero mux0))]
                              [L (ring (add (sub A (mul mu y)) (mul mu x)) L)])
                     (ring (add A (neg s/zero)) A)
                     (call 'signed/add-left-monotone (neg (mul mu y)) (neg s/zero) A
                           (call 'signed/negate-reverses-order s/zero (mul mu y) muy))))))

(defn simplex [N Y] (pconj (s/all-below N (fn [i] (le s/zero (at Y i)))) (eqv (sum Y N) one)))

(defn vi-term [v x Y] (f/lam [['sq-i nat]] (mul (sub (at v 'sq-i) (at x 'sq-i)) (sub (at Y 'sq-i) (at x 'sq-i)))))

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
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-sproj-projection theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
