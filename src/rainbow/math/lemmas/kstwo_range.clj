(ns rainbow.math.lemmas.kstwo-range
  "General lemmas: kstwo range. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.nsfr-reading :as nsfr]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
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

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn drop-nn [x y h] (le-resp (add x (neg y)) (sub x y) (add x (neg s/zero)) x (refl (sub x y)) (ring (add x (neg s/zero)) x)
                                (call 'signed/add-left-monotone (neg y) (neg s/zero) x (call 'signed/negate-reverses-order s/zero y h))))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(def box-spec
  (let [[l r] '[ib-l ib-r] I (nsfr/le-ind l r) goal (pconj (le s/zero I) (le I one))]
    (s/spec 'signed/indicator-box [['ib-l signed] ['ib-r signed]] goal
            (cases (pconj (le l r) (eqv I one)) (pconj (lt r l) (eqv I s/zero)) goal (call 'signed/le-indicator-reading l r)
                   (f/lam [['ib-a (pconj (le l r) (eqv I one))]]
                          (let [e (pright (le l r) (eqv I one) 'ib-a)]
                            (conjoin (le s/zero I) (le I one) (le-resp s/zero s/zero one I (refl s/zero) (sym I one e) zero-le-one) (a/eq-le I one e))))
                   (f/lam [['ib-b (pconj (lt r l) (eqv I s/zero))]]
                          (let [e (pright (lt r l) (eqv I s/zero) 'ib-b)]
                            (conjoin (le s/zero I) (le I one) (a/eq-le s/zero I (sym I s/zero e)) (le-resp s/zero I one one (sym I s/zero e) (refl one) zero-le-one))))))))

(defn count-term [S t] (f/lam [['ic-i nat]] (nsfr/le-ind (at S 'ic-i) t)))

(def count-spec
  (let [[S t n] '[ic-s ic-t ic-n] C (sum (count-term S t) n) ON (f/lam [['ic-o nat]] one) box (fn [i] (call 'signed/indicator-box (at S i) t))]
    (s/spec 'signed/indicator-count-bounds [['ic-s family] ['ic-t signed] ['ic-n nat]]
            (pconj (le s/zero C) (le C (of-nat/of-nat n)))
            (conjoin (le s/zero C) (le C (of-nat/of-nat n))
                     (call 'signed/expr-sum-value-nonnegative (count-term S t) n
                           (f/lam [['ic-j nat] ['ic-h (below 'ic-j n)]] (pleft (le s/zero (nsfr/le-ind (at S 'ic-j) t)) (le (nsfr/le-ind (at S 'ic-j) t) one) (box 'ic-j))))
                     (le-resp C C (sum ON n) (of-nat/of-nat n) (refl C)
                              (trans (sum ON n) (mul one (of-nat/of-nat n)) (of-nat/of-nat n) (call 'signed/expr-sum-constant-of-nat one n)
                                     (call 'signed/multiply-one-left (of-nat/of-nat n)))
                              (a/sum-mono (count-term S t) ON n 'ic-k
                                          (fn [i h] (pright (le s/zero (nsfr/le-ind (at S i) t)) (le (nsfr/le-ind (at S i) t) one) (box i)))))))))

(defn abs-prop [A d] (pconj (disj (eqv A d) (eqv A (neg d))) (le s/zero A)))

(def abs-spec
  (let [[A d] '[ab-a ab-d] X (sub A d) Y (add A d) goal (disj (eqv A d) (eqv A (neg d)))]
    (s/spec 'signed/abs-reading [['ab-a signed] ['ab-d signed] ['ab-1 (le d A)] ['ab-2 (le (neg d) A)] ['ab-p (eqv (mul X Y) s/zero)]]
            (abs-prop A d)
            (conjoin goal (le s/zero A)
                     (cases (eqv X s/zero) (eqv Y s/zero) goal (call 'signed/multiply-zero-split X Y 'ab-p)
                            (f/lam [['ab-x (eqv X s/zero)]] (inl (eqv A d) (eqv A (neg d)) (sym d A (from-diff d A 'ab-x))))
                            (f/lam [['ab-y (eqv Y s/zero)]]
                                   (inr (eqv A d) (eqv A (neg d))
                                        (a/chain A [(sub Y d) (ring A (sub Y d))]
                                                 [(sub s/zero d) (acong Y s/zero (neg d) (neg d) 'ab-y (refl (neg d)))]
                                                 [(neg d) (ring (sub s/zero d) (neg d))]))))
                     ;; 0 ~ d - d <= A + A, and A <= 0 would give A + A <= A
                     (let [aa (le-resp (add d (neg d)) s/zero (add A A) (add A A) (ring (add d (neg d)) s/zero) (refl (add A A))
                                       (call 'signed/add-monotone d A (neg d) A 'ab-1 'ab-2))]
                       (cases (le s/zero A) (le A s/zero) (le s/zero A) (call 'signed/at-most-total s/zero A)
                              (f/lam [['ab-g (le s/zero A)]] 'ab-g)
                              (f/lam [['ab-n (le A s/zero)]]
                                     (le-trans s/zero (add A A) A aa
                                               (le-resp (add A A) (add A A) (add A s/zero) A (refl (add A A)) (ring (add A s/zero) A)
                                                        (call 'signed/add-left-monotone A s/zero A 'ab-n))))))))))

(def bound-spec
  (let [[A F G n m] '[kb-a kb-f kb-g kb-n kb-m] d (sub (mul m F) (mul n G)) NM (mul n m)
        nn-prod (fn [x y hx hy] (le-resp (mul x s/zero) s/zero (mul x y) (mul x y) (ring (mul x s/zero) s/zero) (refl (mul x y)) (lmono x s/zero y hx hy)))
        d-le (le-trans d (mul m F) NM (drop-nn (mul m F) (mul n G) (nn-prod n G 'kb-hn 'kb-g0))
                       (le-resp (mul m F) (mul m F) (mul m n) NM (refl (mul m F)) (ring (mul m n) NM) (lmono m F n 'kb-hm 'kb-fn)))
        nd-le (le-resp (sub (mul n G) (mul m F)) (neg d) NM NM (ring (sub (mul n G) (mul m F)) (neg d)) (refl NM)
                       (le-trans (sub (mul n G) (mul m F)) (mul n G) NM (drop-nn (mul n G) (mul m F) (nn-prod m F 'kb-hm 'kb-f0))
                                 (lmono n G m 'kb-hn 'kb-gm)))]
    (s/spec 'signed/ks-abs-bound
            [['kb-a signed] ['kb-f signed] ['kb-g signed] ['kb-n signed] ['kb-m signed]
             ['kb-e (disj (eqv A d) (eqv A (neg d)))] ['kb-f0 (le s/zero F)] ['kb-fn (le F n)] ['kb-g0 (le s/zero G)] ['kb-gm (le G m)]
             ['kb-hn (le s/zero n)] ['kb-hm (le s/zero m)]]
            (le A NM)
            (cases (eqv A d) (eqv A (neg d)) (le A NM) 'kb-e
                   (f/lam [['kb-1 (eqv A d)]] (le-resp d A NM NM (sym A d 'kb-1) (refl NM) d-le))
                   (f/lam [['kb-2 (eqv A (neg d))]] (le-resp (neg d) A NM NM (sym A (neg d) 'kb-2) (refl NM) nd-le))))))

(defn dev [F G k NL ML] (sub (mul ML (at F k)) (mul NL (at G k))))

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

(def theorem-specs [box-spec count-spec abs-spec bound-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-positive/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-kstwo-range theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
