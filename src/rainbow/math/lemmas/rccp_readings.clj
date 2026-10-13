(ns rainbow.math.lemmas.rccp-readings
  "General lemmas: rccp readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.lemmas.pcmax-lower-bound :as pdep0]
            [rainbow.math.logic.function :as f]
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

(defn pfacts [v w] (pconj (disj (eqv w s/zero) (eqv w v)) (pconj (le s/zero w) (le v w))))

(defn le-of-diff-np [x y h] (le-resp (add (sub x y) y) x (add s/zero y) y (ring (add (sub x y) y) x) (ring (add s/zero y) y)
                                      (call 'signed/add-right-monotone (sub x y) s/zero y h)))

(defn diff-np-of-le [x y h] (le-resp (sub x y) (sub x y) (sub y y) s/zero (refl (sub x y)) (ring (sub y y) s/zero)
                                      (call 'signed/add-right-monotone x y (neg y) h)))

(defn overload-facts [x c O]
  (pconj (pfacts (sub x c) O) (pconj (f/forall [['ov-z (eqv O s/zero)]] (le x c)) (f/forall [['ov-f (le x c)]] (eqv O s/zero)))))

(def overload-spec
  (let [x 'ov-x c 'ov-c O 'ov-O v (sub x c) pv (pp v)
        f* (call 'signed/positive-part-cases v)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        rest-t (pconj (le v pv) (disj (eqv pv s/zero) (eqv pv v)))
        nn (fst (le s/zero pv) rest-t f*)
        lo (fst (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))
        orr (snd (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))
        sO (sym O pv 'ov-h)
        O-nn (le-resp s/zero s/zero pv O (refl s/zero) sO nn)
        v-le-O (le-resp v v pv O (refl v) sO lo)
        O-or (cases (eqv pv s/zero) (eqv pv v) (disj (eqv O s/zero) (eqv O v)) orr
                    (f/lam [['ov-a (eqv pv s/zero)]] (inl (eqv O s/zero) (eqv O v) (trans O pv s/zero 'ov-h 'ov-a)))
                    (f/lam [['ov-b (eqv pv v)]] (inr (eqv O s/zero) (eqv O v) (trans O pv v 'ov-h 'ov-b))))
        zero-fits (f/lam [['ov-z (eqv O s/zero)]] (le-of-diff-np x c (le-resp v v O s/zero (refl v) 'ov-z v-le-O)))
        fits-zero (f/lam [['ov-f (le x c)]]
                         (cases (eqv O s/zero) (eqv O v) (eqv O s/zero) O-or
                                (f/lam [['ov-oz (eqv O s/zero)]] 'ov-oz)
                                (f/lam [['ov-ov (eqv O v)]]
                                       (anti O s/zero (le-resp v O s/zero s/zero (sym O v 'ov-ov) (refl s/zero) (diff-np-of-le x c 'ov-f)) O-nn))))]
    (s/spec 'signed/overload-reading [['ov-x signed] ['ov-c signed] ['ov-O signed] ['ov-h (eqv O pv)]]
            (overload-facts x c O)
            (conjoin (pfacts v O) (pconj (f/forall [['ov-z (eqv O s/zero)]] (le x c)) (f/forall [['ov-f (le x c)]] (eqv O s/zero)))
                     (conjoin (disj (eqv O s/zero) (eqv O v)) (pconj (le s/zero O) (le v O)) O-or
                              (conjoin (le s/zero O) (le v O) O-nn v-le-O))
                     (conjoin (f/forall [['ov-z (eqv O s/zero)]] (le x c)) (f/forall [['ov-f (le x c)]] (eqv O s/zero)) zero-fits fits-zero)))))

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

(def theorem-specs [overload-spec])

(defn extend-environment [checked-environment]
  (-> (pdep0/extend-environment checked-environment)
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-rccp-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
