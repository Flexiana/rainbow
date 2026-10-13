(ns rainbow.math.lemmas.claimpay-readings
  "General lemmas: claimpay readings. The mathematical facts the corresponding checks rest on,
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

(def pp-spec
  (let [v 'pq-v D (call 'signed/decide-at-most s/zero v)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['pq-e (eqb b)]] (pp-facts v (sel s/zero v b))))
        ok (fn [w] (disj (eqv w s/zero) (eqv w v)))]
    (s/spec 'signed/positive-part-cases [['pq-v signed]]
            (pp-facts v (pp v))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['pq-b bool]] (claim 'pq-b))
                          ;; decided false: v <= 0, value 0
                          (f/lam [['pq-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le s/zero s/zero) (pconj (le v s/zero) (ok s/zero)) (eq-le s/zero s/zero (refl s/zero))
                                          (conjoin (le v s/zero) (ok s/zero) (call 'signed/decide-at-most-false-reverse s/zero v 'pq-e)
                                                   (inl (eqv s/zero s/zero) (eqv s/zero v) (refl s/zero)))))
                          ;; decided true: 0 <= v, value v
                          (f/lam [['pq-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le s/zero v) (pconj (le v v) (ok v)) (call 'signed/decide-at-most-true-sound s/zero v 'pq-e)
                                          (conjoin (le v v) (ok v) (eq-le v v (refl v)) (inr (eqv v s/zero) (eqv v v) (refl v)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn cell-facts [L d k E R P]
  (pconj (pconj (disj (eqv E s/zero) (eqv E (sub L d))) (pconj (le s/zero E) (le (sub L d) E)))
         (pconj (pconj (disj (eqv P R) (eqv P k)) (pconj (le P R) (le P k)))
                (pconj (le s/zero P) (le P L)))))

(def cell-spec
  (let [L 'cp-L d 'cp-d c 'cp-c k 'cp-k E 'cp-E R 'cp-R X 'cp-X P 'cp-P
        u (sub L d) w (sub R k)
        ppE (call 'signed/positive-part-cases u) ppX (call 'signed/positive-part-cases w)
        pE (pp u) pX (pp w)
        fst (fn [A B h] (call 'proposition/left A B h)) snd (fn [A B h] (call 'proposition/right A B h))
        ;; facts on E transported along E ~ (L - d)^+
        Ef (pp-facts u pE)
        E-nn (le-resp s/zero s/zero pE E (refl s/zero) (sym E pE 'cp-hE) (fst (le s/zero pE) (pconj (le u pE) (disj (eqv pE s/zero) (eqv pE u))) ppE))
        E-lo (le-resp u u pE E (refl u) (sym E pE 'cp-hE)
                      (fst (le u pE) (disj (eqv pE s/zero) (eqv pE u)) (snd (le s/zero pE) (pconj (le u pE) (disj (eqv pE s/zero) (eqv pE u))) ppE)))
        E-or-pp (snd (le u pE) (disj (eqv pE s/zero) (eqv pE u)) (snd (le s/zero pE) (pconj (le u pE) (disj (eqv pE s/zero) (eqv pE u))) ppE))
        E-or (cases (eqv pE s/zero) (eqv pE u) (disj (eqv E s/zero) (eqv E u)) E-or-pp
                    (f/lam [['cp-e0 (eqv pE s/zero)]] (inl (eqv E s/zero) (eqv E u) (trans E pE s/zero 'cp-hE 'cp-e0)))
                    (f/lam [['cp-e1 (eqv pE u)]] (inr (eqv E s/zero) (eqv E u) (trans E pE u 'cp-hE 'cp-e1))))
        ;; facts on X
        X-nn (le-resp s/zero s/zero pX X (refl s/zero) (sym X pX 'cp-hX) (fst (le s/zero pX) (pconj (le w pX) (disj (eqv pX s/zero) (eqv pX w))) ppX))
        X-lo (le-resp w w pX X (refl w) (sym X pX 'cp-hX)
                      (fst (le w pX) (disj (eqv pX s/zero) (eqv pX w)) (snd (le s/zero pX) (pconj (le w pX) (disj (eqv pX s/zero) (eqv pX w))) ppX)))
        X-or-pp (snd (le w pX) (disj (eqv pX s/zero) (eqv pX w)) (snd (le s/zero pX) (pconj (le w pX) (disj (eqv pX s/zero) (eqv pX w))) ppX))
        ;; P = R - X
        P-le-R (le-resp (sub R X) P (sub R s/zero) R (sym P (sub R X) 'cp-hP) (ring (sub R s/zero) R)
                        (le-resp (add (neg X) R) (sub R X) (add (neg s/zero) R) (sub R s/zero) (ring (add (neg X) R) (sub R X)) (ring (add (neg s/zero) R) (sub R s/zero))
                                 (call 'signed/add-right-monotone (neg X) (neg s/zero) R (call 'signed/negate-reverses-order s/zero X X-nn))))
        P-le-k (le-resp (sub R X) P (sub R w) k (sym P (sub R X) 'cp-hP) (ring (sub R w) k)
                        (le-resp (add (neg X) R) (sub R X) (add (neg w) R) (sub R w) (ring (add (neg X) R) (sub R X)) (ring (add (neg w) R) (sub R w))
                                 (call 'signed/add-right-monotone (neg X) (neg w) R (call 'signed/negate-reverses-order w X X-lo))))
        P-or (cases (eqv pX s/zero) (eqv pX w) (disj (eqv P R) (eqv P k)) X-or-pp
                    (f/lam [['cp-x0 (eqv pX s/zero)]]
                           (inl (eqv P R) (eqv P k)
                                (a/chain P [(sub R X) 'cp-hP]
                                         [(sub R s/zero) (s/add-cong R R (neg X) (neg s/zero) (refl R) (a/neg-cong X s/zero (trans X pX s/zero 'cp-hX 'cp-x0)))]
                                         [R (ring (sub R s/zero) R)])))
                    (f/lam [['cp-x1 (eqv pX w)]]
                           (inr (eqv P R) (eqv P k)
                                (a/chain P [(sub R X) 'cp-hP]
                                         [(sub R w) (s/add-cong R R (neg X) (neg w) (refl R) (a/neg-cong X w (trans X pX w 'cp-hX 'cp-x1)))]
                                         [k (ring (sub R w) k)]))))
        R-nn (le-resp s/zero s/zero (mul c E) R (refl s/zero) (sym R (mul c E) 'cp-hR) (nn-prod c E 'cp-hc E-nn))
        P-nn (cases (eqv P R) (eqv P k) (le s/zero P) P-or
                    (f/lam [['cp-pr (eqv P R)]] (le-resp s/zero s/zero R P (refl s/zero) (sym P R 'cp-pr) R-nn))
                    (f/lam [['cp-pk (eqv P k)]] (le-resp s/zero s/zero k P (refl s/zero) (sym P k 'cp-pk) 'cp-hk)))
        ;; R = c E <= E <= L
        R-le-E (le-resp (mul c E) R (mul one E) E (sym R (mul c E) 'cp-hR) (call 'signed/multiply-one-left E)
                        (call 'signed/scaled-term-at-most E c one E-nn 'cp-hc1))
        E-le-L (cases (eqv E s/zero) (eqv E u) (le E L) E-or
                      (f/lam [['cp-ez (eqv E s/zero)]] (le-resp s/zero E L L (sym E s/zero 'cp-ez) (refl L) 'cp-hL))
                      (f/lam [['cp-eu (eqv E u)]]
                             (le-resp u E L L (sym E u 'cp-eu) (refl L)
                                      (le-resp (add (neg d) L) u (add (neg s/zero) L) L (ring (add (neg d) L) u) (ring (add (neg s/zero) L) L)
                                               (call 'signed/add-right-monotone (neg d) (neg s/zero) L (call 'signed/negate-reverses-order s/zero d 'cp-hd))))))
        P-le-L (le-trans P R L P-le-R (le-trans R E L R-le-E E-le-L))]
    (s/spec 'signed/claim-payment-cell
            [['cp-L signed] ['cp-d signed] ['cp-c signed] ['cp-k signed] ['cp-E signed] ['cp-R signed] ['cp-X signed] ['cp-P signed]
             ['cp-hL (le s/zero L)] ['cp-hd (le s/zero d)] ['cp-hc (le s/zero c)] ['cp-hc1 (le c one)] ['cp-hk (le s/zero k)]
             ['cp-hE (eqv E pE)] ['cp-hR (eqv R (mul c E))] ['cp-hX (eqv X pX)] ['cp-hP (eqv P (sub R X))]]
            (cell-facts L d k E R P)
            (conjoin (pconj (disj (eqv E s/zero) (eqv E u)) (pconj (le s/zero E) (le u E)))
                     (pconj (pconj (disj (eqv P R) (eqv P k)) (pconj (le P R) (le P k))) (pconj (le s/zero P) (le P L)))
                     (conjoin (disj (eqv E s/zero) (eqv E u)) (pconj (le s/zero E) (le u E)) E-or
                              (conjoin (le s/zero E) (le u E) E-nn E-lo))
                     (conjoin (pconj (disj (eqv P R) (eqv P k)) (pconj (le P R) (le P k))) (pconj (le s/zero P) (le P L))
                              (conjoin (disj (eqv P R) (eqv P k)) (pconj (le P R) (le P k)) P-or
                                       (conjoin (le P R) (le P k) P-le-R P-le-k))
                              (conjoin (le s/zero P) (le P L) P-nn P-le-L))))))

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

(def theorem-specs [pp-spec cell-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-claimpay-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
