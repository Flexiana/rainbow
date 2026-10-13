(ns rainbow.math.lemmas.salesq-readings
  "General lemmas: salesq readings. The mathematical facts the corresponding checks rest on,
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

(defn short-sel "the checker's (a <= t ? t - a : 0)" [t av] (sel s/zero (sub t av) (call 'signed/decide-at-most av t)))

(defn flag-sel "the checker's [t <= a]" [t av] (sel s/zero one (call 'signed/decide-at-most t av)))

(defn short-facts [t av sv]
  (pconj (le s/zero sv) (pconj (le (sub t av) sv) (pconj (disj (eqv sv s/zero) (eqv sv (sub t av)))
                                                        (f/forall [['sf-met (le t av)]] (eqv sv s/zero))))))

(defn flag-facts [t av fv] (disj (pconj (eqv fv one) (le t av)) (pconj (eqv fv s/zero) (le av t))))

(def short-spec
  (let [t 'sc-t av 'sc-a sv 'sc-s u (sub t av) D (call 'signed/decide-at-most av t)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['sc-de (eqb b)] ['sc-h (eqv sv (sel s/zero u b))]] (short-facts t av sv)))
        Met (f/forall [['sf-met (le t av)]] (eqv sv s/zero))
        Or (disj (eqv sv s/zero) (eqv sv u))
        pack (fn [nn lo orr met]
               (conjoin (le s/zero sv) (pconj (le u sv) (pconj Or Met)) nn
                        (conjoin (le u sv) (pconj Or Met) lo (conjoin Or Met orr met))))]
    (s/spec 'signed/shortfall-cases [['sc-t signed] ['sc-a signed] ['sc-s signed] ['sc-h (eqv sv (short-sel t av))]]
            (short-facts t av sv)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['sc-b bool]] (claim 'sc-b))
                          ;; decided false: t <= a, s ~ 0
                          (f/lam [['sc-de (eqb (f/const* 'data/false []))] ['sc-h (eqv sv s/zero)]]
                                 (let [t-a (call 'signed/decide-at-most-false-reverse av t 'sc-de)
                                       u-np (le-resp (sub t av) u (sub av av) s/zero (refl u) (ring (sub av av) s/zero)
                                                     (call 'signed/add-right-monotone t av (neg av) t-a))]
                                   (pack (le-resp s/zero s/zero s/zero sv (refl s/zero) (sym sv s/zero 'sc-h) (a/eq-le s/zero s/zero (refl s/zero)))
                                         (le-resp u u s/zero sv (refl u) (sym sv s/zero 'sc-h) u-np)
                                         (inl (eqv sv s/zero) (eqv sv u) 'sc-h)
                                         (f/lam [['sf-met (le t av)]] 'sc-h))))
                          ;; decided true: a <= t, s ~ t - a
                          (f/lam [['sc-de (eqb (f/const* 'data/true []))] ['sc-h (eqv sv u)]]
                                 (let [a-t (call 'signed/decide-at-most-true-sound av t 'sc-de)
                                       u-nn (diff-nn av t a-t)]
                                   (pack (le-resp s/zero s/zero u sv (refl s/zero) (sym sv u 'sc-h) u-nn)
                                         (a/eq-le u sv (sym sv u 'sc-h))
                                         (inr (eqv sv s/zero) (eqv sv u) 'sc-h)
                                         (f/lam [['sf-met (le t av)]]
                                                (trans sv u s/zero 'sc-h
                                                       (a/chain u [(sub av av) (s/add-cong t av (neg av) (neg av) (anti t av 'sf-met a-t) (refl (neg av)))]
                                                                [s/zero (ring (sub av av) s/zero)]))))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'sc-h))))

(def flag-spec
  (let [t 'fc-t av 'fc-a fv 'fc-f D (call 'signed/decide-at-most t av)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['fc-de (eqb b)] ['fc-h (eqv fv (sel s/zero one b))]] (flag-facts t av fv)))
        L (pconj (eqv fv one) (le t av)) R (pconj (eqv fv s/zero) (le av t))]
    (s/spec 'signed/on-target-cases [['fc-t signed] ['fc-a signed] ['fc-f signed] ['fc-h (eqv fv (flag-sel t av))]]
            (flag-facts t av fv)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['fc-b bool]] (claim 'fc-b))
                          (f/lam [['fc-de (eqb (f/const* 'data/false []))] ['fc-h (eqv fv s/zero)]]
                                 (inr L R (conjoin (eqv fv s/zero) (le av t) 'fc-h (call 'signed/decide-at-most-false-reverse t av 'fc-de))))
                          (f/lam [['fc-de (eqb (f/const* 'data/true []))] ['fc-h (eqv fv one)]]
                                 (inl L R (conjoin (eqv fv one) (le t av) 'fc-h (call 'signed/decide-at-most-true-sound t av 'fc-de))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'fc-h))))

(defn rep-facts [t av sv fv]
  (pconj (pconj (le s/zero sv) (pconj (le (sub t av) sv) (disj (eqv sv s/zero) (eqv sv (sub t av)))))
         (disj (pconj (eqv fv one) (eqv sv s/zero)) (pconj (eqv fv s/zero) (le av t)))))

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

(def theorem-specs [short-spec flag-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-salesq-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
