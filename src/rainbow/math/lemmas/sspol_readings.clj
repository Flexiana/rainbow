(ns rainbow.math.lemmas.sspol-readings
  "General lemmas: sspol readings. The mathematical facts the corresponding checks rest on,
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

(defn ind "the checker's [s <= I]" [sv I] (sel s/zero one (call 'signed/decide-at-most sv I)))

(defn order-facts [sv S I o q]
  (pconj (le s/zero o)
         (disj (pconj (le sv I) (pconj (eqv o s/zero) (eqv (add I q) I)))
               (pconj (le I sv) (pconj (eqv o one) (eqv (add I q) S))))))

(def order-spec
  (let [sv 'so-s S 'so-S I 'so-I o 'so-o q 'so-q D (call 'signed/decide-at-most sv I)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['so-de (eqb b)] ['so-ho (eqv o (sub one (sel s/zero one b)))]] (order-facts sv S I o q)))
        L (pconj (le sv I) (pconj (eqv o s/zero) (eqv (add I q) I)))
        R (pconj (le I sv) (pconj (eqv o one) (eqv (add I q) S)))
        G (sub S I)]
    (s/spec 'signed/ss-order-cases [['so-s signed] ['so-S signed] ['so-I signed] ['so-o signed] ['so-q signed]
                                    ['so-ho (eqv o (sub one (ind sv I)))] ['so-hq (eqv q (mul o G))]]
            (order-facts sv S I o q)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['so-b bool]] (claim 'so-b))
                          ;; decided false: I < s, indicator 0, o ~ 1, q ~ S - I
                          (f/lam [['so-de (eqb (f/const* 'data/false []))] ['so-ho (eqv o (sub one s/zero))]]
                                 (let [o1 (trans o (sub one s/zero) one 'so-ho (ring (sub one s/zero) one))
                                       qg (a/chain q [(mul o G) 'so-hq] [(mul one G) (a/mul-cong o one G G o1 (refl G))] [G (call 'signed/multiply-one-left G)])]
                                   (conjoin (le s/zero o) (disj L R) (le-resp s/zero s/zero one o (refl s/zero) (sym o one o1) (f/const* 'signed/zero-at-most-one []))
                                            (inr L R (conjoin (le I sv) (pconj (eqv o one) (eqv (add I q) S)) (call 'signed/decide-at-most-false-reverse sv I 'so-de)
                                                              (conjoin (eqv o one) (eqv (add I q) S) o1
                                                                       (a/chain (add I q) [(add I G) (s/add-cong I I q G (refl I) qg)] [S (ring (add I G) S)])))))))
                          ;; decided true: s <= I, indicator 1, o ~ 0, q ~ 0
                          (f/lam [['so-de (eqb (f/const* 'data/true []))] ['so-ho (eqv o (sub one one))]]
                                 (let [o0 (trans o (sub one one) s/zero 'so-ho (ring (sub one one) s/zero))
                                       q0 (a/chain q [(mul o G) 'so-hq] [(mul s/zero G) (a/mul-cong o s/zero G G o0 (refl G))] [s/zero (ring (mul s/zero G) s/zero)])]
                                   (conjoin (le s/zero o) (disj L R) (a/eq-le s/zero o (sym o s/zero o0))
                                            (inl L R (conjoin (le sv I) (pconj (eqv o s/zero) (eqv (add I q) I)) (call 'signed/decide-at-most-true-sound sv I 'so-de)
                                                              (conjoin (eqv o s/zero) (eqv (add I q) I) o0
                                                                       (a/chain (add I q) [(add I s/zero) (s/add-cong I I q s/zero (refl I) q0)] [I (ring (add I s/zero) I)])))))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'so-ho))))

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
      (support/extend-with-shared :expr-sum-sspol-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
