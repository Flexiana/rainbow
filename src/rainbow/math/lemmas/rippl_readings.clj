(ns rainbow.math.lemmas.rippl-readings
  "General lemmas: rippl readings. The mathematical facts the corresponding checks rest on,
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

(defn pp-parts [v]
  (let [pv (pp v) f* (call 'signed/positive-part-cases v)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        rest-t (pconj (le v pv) (disj (eqv pv s/zero) (eqv pv v)))]
    {:nn (fst (le s/zero pv) rest-t f*)
     :lo (fst (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))
     :or (snd (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))}))

(defn max-facts [m x M1] (pconj (disj (eqv M1 m) (eqv M1 x)) (pconj (le m M1) (le x M1))))

(def step-spec
  (let [m 'rm-m x 'rm-x G 'rm-G M1 'rm-M v (sub x m) pv (pp v) {nn :nn lo :lo orr :or} (pp-parts v)
        sG (sym G pv 'rm-hG)
        G-nn (le-resp s/zero s/zero pv G (refl s/zero) sG nn)
        v-le-G (le-resp v v pv G (refl v) sG lo)
        sM (sym M1 (add m G) 'rm-hM)
        m-le (le-resp (add m s/zero) m (add m G) M1 (ring (add m s/zero) m) sM
                      (le-resp (add s/zero m) (add m s/zero) (add G m) (add m G) (ring (add s/zero m) (add m s/zero)) (ring (add G m) (add m G))
                               (call 'signed/add-right-monotone s/zero G m G-nn)))
        x-le (le-resp (add m v) x (add m G) M1 (ring (add m v) x) sM
                      (le-resp (add v m) (add m v) (add G m) (add m G) (ring (add v m) (add m v)) (ring (add G m) (add m G))
                               (call 'signed/add-right-monotone v G m v-le-G)))
        or* (cases (eqv pv s/zero) (eqv pv v) (disj (eqv M1 m) (eqv M1 x)) orr
                   (f/lam [['rm-z (eqv pv s/zero)]]
                          (inl (eqv M1 m) (eqv M1 x)
                               (a/chain M1 [(add m G) 'rm-hM] [(add m s/zero) (s/add-cong m m G s/zero (refl m) (trans G pv s/zero 'rm-hG 'rm-z))]
                                        [m (ring (add m s/zero) m)])))
                   (f/lam [['rm-v (eqv pv v)]]
                          (inr (eqv M1 m) (eqv M1 x)
                               (a/chain M1 [(add m G) 'rm-hM] [(add m v) (s/add-cong m m G v (refl m) (trans G pv v 'rm-hG 'rm-v))]
                                        [x (ring (add m v) x)]))))]
    (s/spec 'signed/running-max-step [['rm-m signed] ['rm-x signed] ['rm-G signed] ['rm-M signed]
                                      ['rm-hG (eqv G pv)] ['rm-hM (eqv M1 (add m G))]]
            (max-facts m x M1)
            (conjoin (disj (eqv M1 m) (eqv M1 x)) (pconj (le m M1) (le x M1)) or*
                     (conjoin (le m M1) (le x M1) m-le x-le)))))

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

(def theorem-specs [step-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-rippl-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
