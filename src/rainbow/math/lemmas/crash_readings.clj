(ns rainbow.math.lemmas.crash-readings
  "General lemmas: crash readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
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

(def prop-level-0 [:zero])

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn all-below-as [v n pred] (f/forall [[v nat] [(symbol (str v "-h")) (below v n)]] (pred v)))

(defn late-ind [l r] (sel one s/zero (call 'signed/decide-at-most l r)))

(defn late-cases [l r v] (pconj (le s/zero v) (disj (pconj (le l r) (eqv v s/zero)) (eqv v one))))

(def late-spec
  (let [l 'li-l r 'li-r D (call 'signed/decide-at-most l r)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['li-e (eqb b)]] (late-cases l r (sel one s/zero b))))
        ok (fn [v] (disj (pconj (le l r) (eqv v s/zero)) (eqv v one)))]
    (s/spec 'signed/late-indicator-cases [['li-l signed] ['li-r signed]]
            (late-cases l r (late-ind l r))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level-0])
                          (f/lam [['li-b bool]] (claim 'li-b))
                          ;; decided false: value 1
                          (f/lam [['li-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le s/zero one) (ok one) (f/const* 'signed/zero-at-most-one [])
                                          (inr (pconj (le l r) (eqv one s/zero)) (eqv one one) (refl one))))
                          ;; decided true: l <= r, value 0
                          (f/lam [['li-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le s/zero s/zero) (ok s/zero) (a/eq-le s/zero s/zero (refl s/zero))
                                          (inl (pconj (le l r) (eqv s/zero s/zero)) (eqv s/zero one)
                                               (conjoin (le l r) (eqv s/zero s/zero) (call 'signed/decide-at-most-true-sound l r 'li-e) (refl s/zero)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

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

(def theorem-specs [late-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-crash-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
