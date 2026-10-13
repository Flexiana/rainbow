(ns rainbow.math.lemmas.masshaul-readings
  "General lemmas: masshaul readings. The mathematical facts the corresponding checks rest on,
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

(defn split-facts [x P N] (pconj (eqv (sub P N) x) (pconj (le s/zero P) (pconj (le s/zero N) (disj (eqv P s/zero) (eqv N s/zero))))))

(def split-spec
  (let [x 'tp-x P 'tp-P N 'tp-N nx (neg x) {Pnn :nn Plo :lo Por :or} (pp-parts x) {Nnn :nn Nlo :lo Nor :or} (pp-parts nx)
        pP (pp x) pN (pp nx)
        P-nn (le-resp s/zero s/zero pP P (refl s/zero) (sym P pP 'tp-hP) Pnn)
        N-nn (le-resp s/zero s/zero pN N (refl s/zero) (sym N pN 'tp-hN) Nnn)
        x-P (le-resp x x pP P (refl x) (sym P pP 'tp-hP) Plo)
        nx-N (le-resp nx nx pN N (refl nx) (sym N pN 'tp-hN) Nlo)
        goal (split-facts x P N)
        ;; x ~ 0 from x <= 0 and -x <= 0
        xz (fn [x-np nx-np] (anti x s/zero x-np (le-resp (neg s/zero) s/zero (neg nx) x (ring (neg s/zero) s/zero) (ring (neg nx) x)
                                                           (call 'signed/negate-reverses-order nx s/zero nx-np))))
        pack (fn [d orr] (conjoin (eqv (sub P N) x) (pconj (le s/zero P) (pconj (le s/zero N) (disj (eqv P s/zero) (eqv N s/zero)))) d
                                  (conjoin (le s/zero P) (pconj (le s/zero N) (disj (eqv P s/zero) (eqv N s/zero))) P-nn
                                           (conjoin (le s/zero N) (disj (eqv P s/zero) (eqv N s/zero)) N-nn orr))))
        dif (fn [Pv Nv hP hN tail] (a/chain (sub P N) [(sub Pv Nv) (s/add-cong P Pv (neg N) (neg Nv) hP (a/neg-cong N Nv hN))] [x tail]))
        L (eqv P s/zero) R (eqv N s/zero)]
    (s/spec 'signed/two-part-split [['tp-x signed] ['tp-P signed] ['tp-N signed] ['tp-hP (eqv P pP)] ['tp-hN (eqv N pN)]]
            goal
            (cases (eqv pP s/zero) (eqv pP x) goal Por
                   (f/lam [['tp-p0 (eqv pP s/zero)]]
                          (let [p0 (trans P pP s/zero 'tp-hP 'tp-p0)]
                            (cases (eqv pN s/zero) (eqv pN nx) goal Nor
                                   (f/lam [['tp-n0 (eqv pN s/zero)]]
                                          (let [n0 (trans N pN s/zero 'tp-hN 'tp-n0)
                                                x0 (xz (le-resp x x P s/zero (refl x) p0 x-P) (le-resp nx nx N s/zero (refl nx) n0 nx-N))]
                                            (pack (dif s/zero s/zero p0 n0 (trans (sub s/zero s/zero) s/zero x (ring (sub s/zero s/zero) s/zero) (sym x s/zero x0)))
                                                  (inl L R p0))))
                                   (f/lam [['tp-nx (eqv pN nx)]]
                                          (pack (dif s/zero nx p0 (trans N pN nx 'tp-hN 'tp-nx) (ring (sub s/zero nx) x)) (inl L R p0))))))
                   (f/lam [['tp-px (eqv pP x)]]
                          (let [px (trans P pP x 'tp-hP 'tp-px)]
                            (cases (eqv pN s/zero) (eqv pN nx) goal Nor
                                   (f/lam [['tp-n0 (eqv pN s/zero)]]
                                          (let [n0 (trans N pN s/zero 'tp-hN 'tp-n0)]
                                            (pack (dif x s/zero px n0 (ring (sub x s/zero) x)) (inr L R n0))))
                                   (f/lam [['tp-nx (eqv pN nx)]]
                                          (let [nxv (trans N pN nx 'tp-hN 'tp-nx)
                                                x-nn (le-resp s/zero s/zero P x (refl s/zero) px P-nn)
                                                nx-nn (le-resp s/zero s/zero N nx (refl s/zero) nxv N-nn)
                                                x-np (le-resp (neg nx) x (neg s/zero) s/zero (ring (neg nx) x) (ring (neg s/zero) s/zero)
                                                              (call 'signed/negate-reverses-order s/zero nx nx-nn))
                                                x0 (anti x s/zero x-np x-nn)]
                                            (pack (dif x nx px nxv
                                                       (a/chain (sub x nx) [(add x x) (ring (sub x nx) (add x x))]
                                                                [(add s/zero s/zero) (s/add-cong x s/zero x s/zero x0 x0)]
                                                                [s/zero (ring (add s/zero s/zero) s/zero)]
                                                                [x (sym x s/zero x0)]))
                                                  (inl L R (trans P x s/zero px x0))))))))))))

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
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-masshaul-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
