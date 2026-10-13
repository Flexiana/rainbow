(ns rainbow.math.lemmas.xol-readings
  "General lemmas: xol readings. The mathematical facts the corresponding checks rest on,
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

(defn layer [e l] (sel (sel l e (call 'signed/decide-at-most e l)) s/zero (call 'signed/decide-at-most e s/zero)))

(defn layer-cases* [e l V]
  (disj (pconj (le e s/zero) (eqv V s/zero))
        (disj (pconj (le s/zero e) (pconj (le e l) (eqv V e)))
              (pconj (le l e) (eqv V l)))))

(defn layer-facts [e l V] (pconj (le s/zero V) (pconj (le V l) (layer-cases* e l V))))

(def layer-spec
  (let [e 'lc-e l 'lc-l D1 (call 'signed/decide-at-most e s/zero) D2 (call 'signed/decide-at-most e l)
        eqb (fn [D b] (f/equality type-level bool D b))
        fT (f/const* 'data/true []) fF (f/const* 'data/false [])
        A (fn [V] (pconj (le e s/zero) (eqv V s/zero)))
        B (fn [V] (pconj (le s/zero e) (pconj (le e l) (eqv V e))))
        C (fn [V] (pconj (le l e) (eqv V l)))
        ;; inner: given 0 <= e, case on e <= l
        inner-claim (fn [b] (f/forall [['lc-e2 (eqb D2 b)]] (layer-facts e l (sel l e b))))
        inner (fn [e-nn]
                (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                              (f/lam [['lc-b2 bool]] (inner-claim 'lc-b2))
                              ;; e > l: value l
                              (f/lam [['lc-e2 (eqb D2 fF)]]
                                     (let [le-l (call 'signed/decide-at-most-false-reverse e l 'lc-e2)]
                                       (conjoin (le s/zero l) (pconj (le l l) (layer-cases* e l l)) 'lc-hl
                                                (conjoin (le l l) (layer-cases* e l l) (a/eq-le l l (refl l))
                                                         (inr (A l) (disj (B l) (C l)) (inr (B l) (C l) (conjoin (le l e) (eqv l l) le-l (refl l))))))))
                              ;; e <= l: value e
                              (f/lam [['lc-e2 (eqb D2 fT)]]
                                     (let [e-le (call 'signed/decide-at-most-true-sound e l 'lc-e2)]
                                       (conjoin (le s/zero e) (pconj (le e l) (layer-cases* e l e)) e-nn
                                                (conjoin (le e l) (layer-cases* e l e) e-le
                                                         (inr (A e) (disj (B e) (C e)) (inl (B e) (C e) (conjoin (le s/zero e) (pconj (le e l) (eqv e e)) e-nn (conjoin (le e l) (eqv e e) e-le (refl e)))))))))
                              D2)
                       (f/app (f/const* 'equality/reflexive [type-level]) bool D2)))
        outer-claim (fn [b] (f/forall [['lc-e1 (eqb D1 b)]] (layer-facts e l (sel (sel l e D2) s/zero b))))]
    (s/spec 'signed/layer-clamp-cases [['lc-e signed] ['lc-l signed] ['lc-hl (le s/zero l)]]
            (layer-facts e l (layer e l))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['lc-b1 bool]] (outer-claim 'lc-b1))
                          ;; e > 0: the capped value
                          (f/lam [['lc-e1 (eqb D1 fF)]] (inner (call 'signed/decide-at-most-false-reverse e s/zero 'lc-e1)))
                          ;; e <= 0: value 0
                          (f/lam [['lc-e1 (eqb D1 fT)]]
                                 (conjoin (le s/zero s/zero) (pconj (le s/zero l) (layer-cases* e l s/zero)) (a/eq-le s/zero s/zero (refl s/zero))
                                          (conjoin (le s/zero l) (layer-cases* e l s/zero) 'lc-hl
                                                   (inl (A s/zero) (disj (B s/zero) (C s/zero))
                                                        (conjoin (le e s/zero) (eqv s/zero s/zero) (call 'signed/decide-at-most-true-sound e s/zero 'lc-e1) (refl s/zero))))))
                          D1)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D1)))))

(defn cell-facts [x d l R]
  (pconj (layer-cases* (sub x d) l R) (pconj (le s/zero R) (pconj (le R l) (le R x)))))

(def cell-spec
  (let [x 'rc-x d 'rc-d l 'rc-l R 'rc-R e (sub x d) V (layer e l)
        lf (call 'signed/layer-clamp-cases e l 'rc-hl)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        cs (fn [W] (layer-cases* e l W))
        V-nn (fst (le s/zero V) (pconj (le V l) (cs V)) lf)
        V-l (fst (le V l) (cs V) (snd (le s/zero V) (pconj (le V l) (cs V)) lf))
        V-cs (snd (le V l) (cs V) (snd (le s/zero V) (pconj (le V l) (cs V)) lf))
        sV (sym R V 'rc-h)
        tr (fn [P] (fn [h] h))
        ;; transport the cases from V to R
        A (fn [W] (pconj (le e s/zero) (eqv W s/zero)))
        B (fn [W] (pconj (le s/zero e) (pconj (le e l) (eqv W e))))
        C (fn [W] (pconj (le l e) (eqv W l)))
        R-cs (cases (A V) (disj (B V) (C V)) (cs R) V-cs
                    (f/lam [['rc-a (A V)]] (inl (A R) (disj (B R) (C R))
                                                (conjoin (le e s/zero) (eqv R s/zero) (fst (le e s/zero) (eqv V s/zero) 'rc-a)
                                                         (trans R V s/zero 'rc-h (snd (le e s/zero) (eqv V s/zero) 'rc-a)))))
                    (f/lam [['rc-bc (disj (B V) (C V))]]
                           (inr (A R) (disj (B R) (C R))
                                (cases (B V) (C V) (disj (B R) (C R)) 'rc-bc
                                       (f/lam [['rc-b (B V)]]
                                              (let [ev (snd (le e l) (eqv V e) (snd (le s/zero e) (pconj (le e l) (eqv V e)) 'rc-b))]
                                                (inl (B R) (C R) (conjoin (le s/zero e) (pconj (le e l) (eqv R e)) (fst (le s/zero e) (pconj (le e l) (eqv V e)) 'rc-b)
                                                                          (conjoin (le e l) (eqv R e) (fst (le e l) (eqv V e) (snd (le s/zero e) (pconj (le e l) (eqv V e)) 'rc-b))
                                                                                   (trans R V e 'rc-h ev))))))
                                       (f/lam [['rc-c (C V)]]
                                              (inr (B R) (C R) (conjoin (le l e) (eqv R l) (fst (le l e) (eqv V l) 'rc-c)
                                                                        (trans R V l 'rc-h (snd (le l e) (eqv V l) 'rc-c)))))))))
        R-nn (le-resp s/zero s/zero V R (refl s/zero) sV V-nn)
        R-l (le-resp V R l l sV (refl l) V-l)
        ;; e = x - d <= x
        e-x (le-resp (add (neg d) x) e (add (neg s/zero) x) x (ring (add (neg d) x) e) (ring (add (neg s/zero) x) x)
                     (call 'signed/add-right-monotone (neg d) (neg s/zero) x (call 'signed/negate-reverses-order s/zero d 'rc-hd)))
        R-x (cases (A R) (disj (B R) (C R)) (le R x) R-cs
                   (f/lam [['rd-a (A R)]] (le-resp s/zero R x x (sym R s/zero (snd (le e s/zero) (eqv R s/zero) 'rd-a)) (refl x) 'rc-hx))
                   (f/lam [['rd-bc (disj (B R) (C R))]]
                          (cases (B R) (C R) (le R x) 'rd-bc
                                 (f/lam [['rd-b (B R)]] (le-resp e R x x (sym R e (snd (le e l) (eqv R e) (snd (le s/zero e) (pconj (le e l) (eqv R e)) 'rd-b))) (refl x) e-x))
                                 (f/lam [['rd-c (C R)]] (le-resp l R x x (sym R l (snd (le l e) (eqv R l) 'rd-c)) (refl x)
                                                                 (le-trans l e x (fst (le l e) (eqv R l) 'rd-c) e-x))))))]
    (s/spec 'signed/layer-recovery-cell
            [['rc-x signed] ['rc-d signed] ['rc-l signed] ['rc-R signed]
             ['rc-hx (le s/zero x)] ['rc-hd (le s/zero d)] ['rc-hl (le s/zero l)] ['rc-h (eqv R V)]]
            (cell-facts x d l R)
            (conjoin (cs R) (pconj (le s/zero R) (pconj (le R l) (le R x))) R-cs
                     (conjoin (le s/zero R) (pconj (le R l) (le R x)) R-nn
                              (conjoin (le R l) (le R x) R-l R-x))))))

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

(def theorem-specs [layer-spec cell-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-xol-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
