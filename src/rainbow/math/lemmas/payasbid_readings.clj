(ns rainbow.math.lemmas.payasbid-readings
  "General lemmas: payasbid readings. The mathematical facts the corresponding checks rest on,
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

(def max-reading-spec
  (let [r 'mx-r a 'mx-a b 'mx-b U (sub r a) W (sub r b) L (eqv r a) Rt (eqv r b)
        prod0 (anti (mul U W) s/zero 'mx-hv (nn-prod U W (diff-nn a r 'mx-ha) (diff-nn b r 'mx-hb)))]
    (s/spec 'signed/max-reading-from-product
            [['mx-r signed] ['mx-a signed] ['mx-b signed] ['mx-ha (le a r)] ['mx-hb (le b r)] ['mx-hv (le (mul U W) s/zero)]]
            (disj L Rt)
            (cases (eqv U s/zero) (eqv W s/zero) (disj L Rt) (call 'signed/multiply-zero-split U W prod0)
                   (f/lam [['mx-u (eqv U s/zero)]] (inl L Rt (sym a r (from-diff a r 'mx-u))))
                   (f/lam [['mx-w (eqv W s/zero)]] (inr L Rt (sym b r (from-diff b r 'mx-w))))))))

(def min-reading-spec
  (let [x 'mn-x a 'mn-a b 'mn-b U (sub x a) W (sub x b) L (eqv x a) Rt (eqv x b)
        pos (le-resp s/zero s/zero (mul (sub a x) (sub b x)) (mul U W) (refl s/zero) (ring (mul (sub a x) (sub b x)) (mul U W))
                     (nn-prod (sub a x) (sub b x) (diff-nn x a 'mn-ha) (diff-nn x b 'mn-hb)))
        prod0 (anti (mul U W) s/zero 'mn-hv pos)]
    (s/spec 'signed/min-reading-from-product
            [['mn-x signed] ['mn-a signed] ['mn-b signed] ['mn-ha (le x a)] ['mn-hb (le x b)] ['mn-hv (le (mul U W) s/zero)]]
            (disj L Rt)
            (cases (eqv U s/zero) (eqv W s/zero) (disj L Rt) (call 'signed/multiply-zero-split U W prod0)
                   (f/lam [['mn-u (eqv U s/zero)]] (inl L Rt (sym a x (from-diff a x 'mn-u))))
                   (f/lam [['mn-w (eqv W s/zero)]] (inr L Rt (sym b x (from-diff b x 'mn-w))))))))

(def scaled-term-spec
  (let [x 'st-x c 'st-c d 'st-d]
    (s/spec 'signed/scaled-term-at-most [['st-x signed] ['st-c signed] ['st-d signed] ['st-hx (le s/zero x)] ['st-hc (le c d)]]
            (le (mul c x) (mul d x))
            (le-resp (mul x c) (mul c x) (mul x d) (mul d x) (ring (mul x c) (mul c x)) (ring (mul x d) (mul d x))
                     (lmono x c d 'st-hx 'st-hc)))))

(def generic-specs [max-reading-spec min-reading-spec scaled-term-spec])

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

(def theorem-specs [max-reading-spec min-reading-spec scaled-term-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-payasbid-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
