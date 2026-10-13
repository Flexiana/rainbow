(ns rainbow.math.lemmas.battery-readings
  "General lemmas: battery readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]))

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

(defn mcong [x xh y yh h k] (call 'signed/multiply-respects-equivalence x xh y yh h k))

(defn acong [x xh y yh h k] (call 'signed/add-respects-equivalence x xh y yh h k))

(defn ring-atoms
  "ring-eq on x ~ y over fresh atoms, applied back to the given terms: [[atom term] ...] (ring-eq's proof
  size explodes with the number of atoms and their degree, so every rearrangement here is over <= 4 atoms)"
  [pairs x y]
  (reduce (fn [t [_ term]] (f/app t term)) (f/lam (mapv (fn [[v _]] [v signed]) pairs) (ring x y)) pairs))

(def step-spec
  (let [[S S1 e c d] '[bs-s bs-s1 bs-e bs-c bs-d] EC (mul e c) x0 (sub S1 S) flow (add S (add EC (neg d)))
        h0 (trans x0 (sub flow S) (add EC (neg d)) (acong S1 flow (neg S) (neg S) 'bs-h (refl (neg S)))
                  (ring-atoms [['ba-s S] ['ba-e EC] ['ba-d d]] (sub (add 'ba-s (add 'ba-e (neg 'ba-d))) 'ba-s) (add 'ba-e (neg 'ba-d))))
        hec (le-resp EC EC (mul one c) c (refl EC) (call 'signed/multiply-one-left c) (call 'signed/scaled-term-at-most c e one 'bs-hc 'bs-he))]
    (s/spec 'signed/battery-step-bound
            [[S signed] [S1 signed] [e signed] [c signed] [d signed]
             ['bs-h (eqv S1 flow)] ['bs-hc (le s/zero c)] ['bs-he (le e one)]]
            (le x0 (sub c d))
            (le-resp (add EC (neg d)) x0 (sub c d) (sub c d) (sym x0 (add EC (neg d)) h0) (refl (sub c d))
                     (call 'signed/add-right-monotone EC c (neg d) hec)))))

(defn gain-family [Sf] (f/lam [['tq nat]] (sub (at Sf (s/succ 'tq)) (at Sf 'tq))))

(defn net-family [cf df] (f/lam [['bn-t nat]] (sub (at cf 'bn-t) (at df 'bn-t))))

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
      unit-laws/extend-environment
      map-sum/extend-environment
      (support/extend-with-shared :expr-sum-battery-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
