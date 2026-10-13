(ns rainbow.math.lemmas.ista-shrink
  "General lemmas: ista shrink. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.square-zero :as square-zero]
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

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

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

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn drop-nn [x y h] (le-resp (add x (neg y)) (sub x y) (add x (neg s/zero)) x (refl (sub x y)) (ring (add x (neg s/zero)) x)
                                (call 'signed/add-left-monotone (neg y) (neg s/zero) x (call 'signed/negate-reverses-order s/zero y h))))

(defn diff-np [x y h] (le-resp (sub x y) (sub x y) (sub y y) s/zero (refl (sub x y)) (ring (sub y y) s/zero) (call 'signed/add-right-monotone x y (neg y) h)))

(defn reading-prop [A Y M X C]
  (let [G (sub A C)]
    (pconj (pconj (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)))
           (pconj (le M A)
                  (pconj (le (mul X X) (mul Y Y))
                         (f/forall [['st-z (le A C)]] (eqv X s/zero)))))))

(def reading-spec
  (let [[A Y M X C] '[st-a st-y st-m st-x st-c]
        G (sub A C) B (sub M G)
        mx (cases (eqv M s/zero) (eqv B s/zero) (disj (eqv M s/zero) (eqv M G)) (call 'signed/multiply-zero-split M B 'st-hp)
                  (f/lam [['st-0 (eqv M s/zero)]] (inl (eqv M s/zero) (eqv M G) 'st-0))
                  (f/lam [['st-1 (eqv B s/zero)]] (inr (eqv M s/zero) (eqv M G) (sym G M (from-diff G M 'st-1)))))
        m-le-a (cases (eqv M s/zero) (eqv M G) (le M A) mx
                      (f/lam [['st-2 (eqv M s/zero)]] (le-resp s/zero M A A (sym M s/zero 'st-2) (refl A) 'st-ha))
                      (f/lam [['st-3 (eqv M G)]] (le-resp G M A A (sym M G 'st-3) (refl A) (drop-nn A C 'st-hc))))
        ;; m m <= a a, so x x ~ m m <= a a ~ y y
        mm-aa (le-trans (mul M M) (mul M A) (mul A A) (lmono M M A 'st-hm m-le-a) (rmono A M A 'st-ha m-le-a))
        shrink (le-resp (mul M M) (mul X X) (mul A A) (mul Y Y) (sym (mul X X) (mul M M) 'st-hx) 'st-hy mm-aa)
        dead (f/lam [['st-z (le A C)]]
                    (let [g-np (diff-np A C 'st-z)
                          m0 (cases (eqv M s/zero) (eqv M G) (eqv M s/zero) mx
                                    (f/lam [['st-4 (eqv M s/zero)]] 'st-4)
                                    (f/lam [['st-5 (eqv M G)]]
                                           (anti M s/zero (le-resp G M s/zero s/zero (sym M G 'st-5) (refl s/zero) g-np) 'st-hm)))
                          xx0 (a/chain (mul X X) [(mul M M) 'st-hx]
                                       [(mul s/zero s/zero) (a/mul-cong M s/zero M s/zero m0 m0)]
                                       [s/zero (ring (mul s/zero s/zero) s/zero)])]
                      (call 'signed/square-zero-reflects X xx0)))]
    (s/spec 'signed/soft-threshold-reading
            [['st-a signed] ['st-y signed] ['st-m signed] ['st-x signed] ['st-c signed]
             ['st-ha (le s/zero A)] ['st-hy (eqv (mul A A) (mul Y Y))] ['st-hg (le G M)] ['st-hm (le s/zero M)]
             ['st-hp (eqv (mul M B) s/zero)] ['st-hx (eqv (mul X X) (mul M M))] ['st-hc (le s/zero C)]]
            (reading-prop A Y M X C)
            (conjoin (pconj (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)))
                     (pconj (le M A) (pconj (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero))))
                     (conjoin (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)) mx (conjoin (le s/zero M) (le G M) 'st-hm 'st-hg))
                     (conjoin (le M A) (pconj (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero))) m-le-a
                              (conjoin (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero)) shrink dead))))))

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

(def theorem-specs [reading-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      square-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-ista-shrink theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
