(ns rainbow.math.lemmas.infnorm-abs
  "General lemmas: infnorm abs. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
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

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q)) (lmono p s/zero q hp hq)))

(defn neg-le [x h] (le-trans (neg x) s/zero x
                              (le-resp (neg x) (neg x) (neg s/zero) s/zero (refl (neg x)) (ring (neg s/zero) s/zero)
                                       (call 'signed/negate-reverses-order s/zero x h))
                              h))

(defn split-prop [A P N]
  (pconj (disj (pconj (eqv P A) (eqv N s/zero)) (pconj (eqv P s/zero) (eqv N (neg A))))
         (pconj (le A (add P N)) (le (neg A) (add P N)))))

(def split-spec
  (let [[A P N] '[ss-a ss-p ss-n]
        L (pconj (eqv P A) (eqv N s/zero)) R (pconj (eqv P s/zero) (eqv N (neg A)))
        prod0 (anti (mul P N) s/zero 'ss-h (nn-prod P N 'ss-0 'ss-1))
        parts (cases (eqv P s/zero) (eqv N s/zero) (disj L R) (call 'signed/multiply-zero-split P N prod0)
                     (f/lam [['ss-pz (eqv P s/zero)]]
                            (inr L R (conjoin (eqv P s/zero) (eqv N (neg A)) 'ss-pz
                                              (sym (neg A) N (a/chain (neg A)
                                                                      [(neg (sub P N)) (a/neg-cong A (sub P N) 'ss-e)]
                                                                      [(neg (sub s/zero N)) (a/neg-cong (sub P N) (sub s/zero N) (acong P s/zero (neg N) (neg N) 'ss-pz (refl (neg N))))]
                                                                      [N (ring (neg (sub s/zero N)) N)])))))
                     (f/lam [['ss-nz (eqv N s/zero)]]
                            (inl L R (conjoin (eqv P A) (eqv N s/zero)
                                              (sym A P (a/chain A [(sub P N) 'ss-e]
                                                                [(sub P s/zero) (acong P P (neg N) (neg s/zero) (refl P) (a/neg-cong N s/zero 'ss-nz))]
                                                                [P (ring (sub P s/zero) P)]))
                                              'ss-nz))))
        up (le-resp (sub P N) A (add P N) (add P N) (sym A (sub P N) 'ss-e) (refl (add P N))
                    (call 'signed/add-left-monotone (neg N) N P (neg-le N 'ss-1)))
        dn (le-resp (add N (neg P)) (neg A) (add N P) (add P N)
                    (a/chain (add N (neg P)) [(neg (sub P N)) (ring (add N (neg P)) (neg (sub P N)))]
                             [(neg A) (a/neg-cong (sub P N) A (sym A (sub P N) 'ss-e))])
                    (ring (add N P) (add P N))
                    (call 'signed/add-left-monotone (neg P) P N (neg-le P 'ss-0)))]
    (s/spec 'signed/sign-split-reading
            [['ss-a signed] ['ss-p signed] ['ss-n signed] ['ss-0 (le s/zero P)] ['ss-1 (le s/zero N)]
             ['ss-e (eqv A (sub P N))] ['ss-h (le (mul P N) s/zero)]]
            (split-prop A P N)
            (conjoin (disj L R) (pconj (le A (add P N)) (le (neg A) (add P N))) parts
                     (conjoin (le A (add P N)) (le (neg A) (add P N)) up dn)))))

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

(def theorem-specs [split-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-infnorm-abs theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
