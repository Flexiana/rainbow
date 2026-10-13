(ns rainbow.math.lemmas.basestock-readings
  "General lemmas: basestock readings. The mathematical facts the corresponding checks rest on,
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

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn pp "the checker's max(0, v): if-at-most 0 v v 0" [v] (sel s/zero v (call 'signed/decide-at-most s/zero v)))

(defn pp-facts [v w] (pconj (le s/zero w) (pconj (le v w) (disj (eqv w s/zero) (eqv w v)))))

(defn eq-le [x y h] (a/eq-le x y h))

(defn gap [S x y] (add S (add (neg x) (neg y))))

(defn pos [x y w] (add x (add y w)))

(defn order-facts [S x y w] (pconj (le s/zero w) (pconj (le S (pos x y w)) (disj (eqv (pos x y w) S) (eqv w s/zero)))))

(defn pp-parts [v]
  (let [pv (pp v) f* (call 'signed/positive-part-cases v)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        rest-t (pconj (le v pv) (disj (eqv pv s/zero) (eqv pv v)))]
    {:nn (fst (le s/zero pv) rest-t f*)
     :lo (fst (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))
     :or (snd (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))}))

(def order-spec
  (let [S 'ou-S x 'ou-x y 'ou-y w 'ou-w g (gap S x y) pg (pp g) {nn :nn lo :lo orr :or} (pp-parts g)
        sw (sym w pg 'ou-h) P (pos x y w) base (add x y)
        w-nn (le-resp s/zero s/zero pg w (refl s/zero) sw nn)
        g-le-w (le-resp g g pg w (refl g) sw lo)
        S-le (le-resp (add g base) S (add w base) P (ring (add g base) S) (ring (add w base) P)
                      (call 'signed/add-right-monotone g w base g-le-w))
        or* (cases (eqv pg s/zero) (eqv pg g) (disj (eqv P S) (eqv w s/zero)) orr
                   (f/lam [['ou-z (eqv pg s/zero)]] (inr (eqv P S) (eqv w s/zero) (trans w pg s/zero 'ou-h 'ou-z)))
                   (f/lam [['ou-g (eqv pg g)]]
                          (inl (eqv P S) (eqv w s/zero)
                               (a/chain P [(pos x y g) (s/add-cong x x (add y w) (add y g) (refl x) (s/add-cong y y w g (refl y) (trans w pg g 'ou-h 'ou-g)))]
                                        [S (ring (pos x y g) S)]))))]
    (s/spec 'signed/order-up-to-reading [['ou-S signed] ['ou-x signed] ['ou-y signed] ['ou-w signed] ['ou-h (eqv w pg)]]
            (order-facts S x y w)
            (conjoin (le s/zero w) (pconj (le S P) (disj (eqv P S) (eqv w s/zero))) w-nn
                     (conjoin (le S P) (disj (eqv P S) (eqv w s/zero)) S-le or*)))))

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

(def theorem-specs [order-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-basestock-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
