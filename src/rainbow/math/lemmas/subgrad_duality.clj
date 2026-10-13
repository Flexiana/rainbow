(ns rainbow.math.lemmas.subgrad-duality
  "General lemmas: subgrad duality. The mathematical facts the corresponding checks rest on,
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

(defn mcong [a b c d h k] (a/mul-cong a b c d h k))

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

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q)) (lmono p s/zero q hp hq)))

(defn one-right [r] (trans (mul r one) (mul one r) r (call 'signed/multiply-commutative r one) (call 'signed/multiply-one-left r)))

(def box-minimiser-spec
  (let [[r x z] '[bm-r bm-x bm-z] goal (le (mul r x) (mul r z))]
    (s/spec 'signed/zero-one-box-minimiser
            [['bm-r signed] ['bm-x signed] ['bm-z signed] ['bm-b (disj (eqv x s/zero) (eqv x one))]
             ['bm-1 (le (mul x r) s/zero)] ['bm-2 (le s/zero (mul r (sub one x)))] ['bm-z0 (le s/zero z)] ['bm-z1 (le z one)]]
            goal
            (cases (eqv x s/zero) (eqv x one) goal 'bm-b
                   (f/lam [['bm-e0 (eqv x s/zero)]]
                          (let [r1 (a/chain (mul r (sub one x))
                                            [(mul r (sub one s/zero)) (mcong r r (sub one x) (sub one s/zero) (refl r)
                                                                             (acong one one (neg x) (neg s/zero) (refl one) (a/neg-cong x s/zero 'bm-e0)))]
                                            [(mul r one) (mcong r r (sub one s/zero) one (refl r) (ring (sub one s/zero) one))]
                                            [r (one-right r)])
                                r-nn (le-resp s/zero s/zero (mul r (sub one x)) r (refl s/zero) r1 'bm-2)]
                            (le-resp (mul r s/zero) (mul r x) (mul r z) (mul r z) (mcong r r s/zero x (refl r) (sym x s/zero 'bm-e0)) (refl (mul r z))
                                     (lmono r s/zero z r-nn 'bm-z0))))
                   (f/lam [['bm-e1 (eqv x one)]]
                          (let [xr (a/chain (mul x r) [(mul one r) (mcong x one r r 'bm-e1 (refl r))] [r (call 'signed/multiply-one-left r)])
                                r-np (le-resp (mul x r) r s/zero s/zero xr (refl s/zero) 'bm-1)
                                nr-nn (le-resp (neg s/zero) s/zero (neg r) (neg r) (ring (neg s/zero) s/zero) (refl (neg r))
                                               (call 'signed/negate-reverses-order r s/zero r-np))
                                ;; -((-r) 1) <= -((-r) z)
                                flip (call 'signed/negate-reverses-order (mul (neg r) z) (mul (neg r) one) (lmono (neg r) z one nr-nn 'bm-z1))
                                lhs (a/chain (neg (mul (neg r) one))
                                             [(neg (neg r)) (a/neg-cong (mul (neg r) one) (neg r) (one-right (neg r)))]
                                             [r (ring (neg (neg r)) r)]
                                             [(mul r one) (sym (mul r one) r (one-right r))]
                                             [(mul r x) (mcong r r one x (refl r) (sym x one 'bm-e1))])]
                            (le-resp (neg (mul (neg r) one)) (mul r x) (neg (mul (neg r) z)) (mul r z)
                                     lhs (ring (neg (mul (neg r) z)) (mul r z)) flip)))))))

(defn pw [u Z] (f/lam [['sp-j nat]] (mul (at u 'sp-j) (at Z 'sp-j))))

(defn AZ [A Z p i] (sum (f/lam [['sa-j nat]] (mul (A i 'sa-j) (at Z 'sa-j))) p))

(defn box [p Z] (s/all-below p (fn [j] (pconj (le s/zero (at Z j)) (le (at Z j) one)))))

(defn step [lam g t i] (add (at lam i) (mul t (at g i))))

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

(def theorem-specs [box-minimiser-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-subgrad-duality theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
