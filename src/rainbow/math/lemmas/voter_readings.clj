(ns rainbow.math.lemmas.voter-readings
  "General lemmas: voter readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.fulfil-readings :as ful]
            [rainbow.math.lemmas.nsfr-reading :as nsfr]
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

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn mn [x y] (ful/msel x y))

(defn mx "the checker's max(x, y): if-at-most x y y x" [x y] (sel x y (call 'signed/decide-at-most x y)))

(defn max-facts [x y v] (pconj (le x v) (pconj (le y v) (disj (eqv v x) (eqv v y)))))

(def max-select-spec
  (let [x 'mz-x y 'mz-y D (call 'signed/decide-at-most x y)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['mz-e (eqb b)]] (max-facts x y (sel x y b))))]
    (s/spec 'signed/max-select-cases [['mz-x signed] ['mz-y signed]]
            (max-facts x y (mx x y))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['mz-b bool]] (claim 'mz-b))
                          ;; decided false: y <= x, value x
                          (f/lam [['mz-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le x x) (pconj (le y x) (disj (eqv x x) (eqv x y))) (a/eq-le x x (refl x))
                                          (conjoin (le y x) (disj (eqv x x) (eqv x y)) (call 'signed/decide-at-most-false-reverse x y 'mz-e)
                                                   (inl (eqv x x) (eqv x y) (refl x)))))
                          ;; decided true: x <= y, value y
                          (f/lam [['mz-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le x y) (pconj (le y y) (disj (eqv y x) (eqv y y))) (call 'signed/decide-at-most-true-sound x y 'mz-e)
                                          (conjoin (le y y) (disj (eqv y x) (eqv y y)) (a/eq-le y y (refl y)) (inr (eqv y x) (eqv y y) (refl y)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn med [x y z] (mx (mn x y) (mn (mx x y) z)))

(defn spr [x y z] (sub (mx x (mx y z)) (mn x (mn y z))))

(defn cell-facts [x y z m sv fv T]
  (pconj (disj (eqv m x) (disj (eqv m y) (eqv m z)))
         (pconj (le (mn x y) m) (pconj (le m (mx x y)) (pconj (le s/zero sv) (nsfr/reading sv T fv))))))

(def cell-spec
  (let [x 'vc-a y 'vc-b z 'vc-c m 'vc-m sv 'vc-s fv 'vc-f T 'vc-T
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        ;; destructure min/max facts
        minp (fn [u v] (let [w (mn u v) f* (call 'signed/min-select-cases u v) R (pconj (le w v) (disj (eqv w u) (eqv w v)))]
                         {:v w :lo-u (fst (le w u) R f*) :lo-v (fst (le w v) (disj (eqv w u) (eqv w v)) (snd (le w u) R f*))
                          :or (snd (le w v) (disj (eqv w u) (eqv w v)) (snd (le w u) R f*))}))
        maxp (fn [u v] (let [w (mx u v) f* (call 'signed/max-select-cases u v) R (pconj (le v w) (disj (eqv w u) (eqv w v)))]
                         {:v w :hi-u (fst (le u w) R f*) :hi-v (fst (le v w) (disj (eqv w u) (eqv w v)) (snd (le u w) R f*))
                          :or (snd (le v w) (disj (eqv w u) (eqv w v)) (snd (le u w) R f*))}))
        P (minp x y) M (maxp x y) Rr (minp (:v M) z) Md (maxp (:v P) (:v Rr))
        p (:v P) Mv (:v M) r (:v Rr) md (:v Md)
        Disj3 (disj (eqv m x) (disj (eqv m y) (eqv m z)))
        d1 (fn [h] (inl (eqv m x) (disj (eqv m y) (eqv m z)) h))
        d2 (fn [h] (inr (eqv m x) (disj (eqv m y) (eqv m z)) (inl (eqv m y) (eqv m z) h)))
        d3 (fn [h] (inr (eqv m x) (disj (eqv m y) (eqv m z)) (inr (eqv m y) (eqv m z) h)))
        which (cases (eqv md p) (eqv md r) Disj3 (:or Md)
                     (f/lam [['vc-mp (eqv md p)]]
                            (let [mp (trans m md p 'vc-hm 'vc-mp)]
                              (cases (eqv p x) (eqv p y) Disj3 (:or P)
                                     (f/lam [['vc-px (eqv p x)]] (d1 (trans m p x mp 'vc-px)))
                                     (f/lam [['vc-py (eqv p y)]] (d2 (trans m p y mp 'vc-py))))))
                     (f/lam [['vc-mr (eqv md r)]]
                            (let [mr (trans m md r 'vc-hm 'vc-mr)]
                              (cases (eqv r Mv) (eqv r z) Disj3 (:or Rr)
                                     (f/lam [['vc-rM (eqv r Mv)]]
                                            (let [mM (trans m r Mv mr 'vc-rM)]
                                              (cases (eqv Mv x) (eqv Mv y) Disj3 (:or M)
                                                     (f/lam [['vc-Mx (eqv Mv x)]] (d1 (trans m Mv x mM 'vc-Mx)))
                                                     (f/lam [['vc-My (eqv Mv y)]] (d2 (trans m Mv y mM 'vc-My))))))
                                     (f/lam [['vc-rz (eqv r z)]] (d3 (trans m r z mr 'vc-rz)))))))
        sm (sym m md 'vc-hm)
        lo (le-resp p p md m (refl p) sm (:hi-u Md))
        hi (cases (eqv md p) (eqv md r) (le m Mv) (:or Md)
                  (f/lam [['vd-mp (eqv md p)]] (le-resp p m Mv Mv (sym m p (trans m md p 'vc-hm 'vd-mp)) (refl Mv) (le-trans p x Mv (:lo-u P) (:hi-u M))))
                  (f/lam [['vd-mr (eqv md r)]] (le-resp r m Mv Mv (sym m r (trans m md r 'vc-hm 'vd-mr)) (refl Mv) (:lo-u Rr))))
        X (maxp y z) X3 (maxp x (:v X)) Y (minp y z) Y3 (minp x (:v Y))
        sp-nn (le-resp s/zero s/zero (sub (:v X3) (:v Y3)) sv (refl s/zero) (sym sv (sub (:v X3) (:v Y3)) 'vc-hs)
                       (diff-nn (:v Y3) (:v X3) (le-trans (:v Y3) x (:v X3) (:lo-u Y3) (:hi-u X3))))
        rd (call 'signed/le-indicator-reading sv T)
        li (nsfr/le-ind sv T)
        A (fn [w] (pconj (le sv T) (eqv w one))) B (fn [w] (pconj (call 'signed/less-than T sv) (eqv w s/zero)))
        rdf (cases (A li) (B li) (nsfr/reading sv T fv) rd
                   (f/lam [['ve-a (A li)]] (inl (A fv) (B fv) (conjoin (le sv T) (eqv fv one) (fst (le sv T) (eqv li one) 've-a)
                                                                        (trans fv li one 'vc-hf (snd (le sv T) (eqv li one) 've-a)))))
                   (f/lam [['ve-b (B li)]] (inr (A fv) (B fv) (conjoin (call 'signed/less-than T sv) (eqv fv s/zero) (fst (call 'signed/less-than T sv) (eqv li s/zero) 've-b)
                                                                        (trans fv li s/zero 'vc-hf (snd (call 'signed/less-than T sv) (eqv li s/zero) 've-b))))))]
    (s/spec 'signed/voter-cell [['vc-a signed] ['vc-b signed] ['vc-c signed] ['vc-m signed] ['vc-s signed] ['vc-f signed] ['vc-T signed]
                                ['vc-hm (eqv m (med x y z))] ['vc-hs (eqv sv (spr x y z))] ['vc-hf (eqv fv (nsfr/le-ind sv T))]]
            (cell-facts x y z m sv fv T)
            (conjoin Disj3 (pconj (le p m) (pconj (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv)))) which
                     (conjoin (le p m) (pconj (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv))) lo
                              (conjoin (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv)) hi
                                       (conjoin (le s/zero sv) (nsfr/reading sv T fv) sp-nn rdf)))))))

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

(def theorem-specs [max-select-spec cell-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-voter-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
