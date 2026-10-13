(ns rainbow.math.lemmas.nvcost-readings
  "General lemmas: nvcost readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.lemmas.pcmax-lower-bound :as pdep0]
            [rainbow.math.logic.function :as f]
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

(def split-spec
  (let [x 'ps-a y 'ps-b O 'ps-O U 'ps-U u (sub x y) w (sub y x) pO (pp u) pU (pp w)
        fO (call 'signed/positive-part-cases u) fU (call 'signed/positive-part-cases w)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        parts (fn [v pv f*]
                (let [rest-t (pconj (le v pv) (disj (eqv pv s/zero) (eqv pv v)))]
                  {:nn (fst (le s/zero pv) rest-t f*)
                   :lo (fst (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))
                   :or (snd (le v pv) (disj (eqv pv s/zero) (eqv pv v)) (snd (le s/zero pv) rest-t f*))}))
        PO (parts u pO fO) PU (parts w pU fU)
        ;; transported to O and U
        O-nn (le-resp s/zero s/zero pO O (refl s/zero) (sym O pO 'ps-hO) (:nn PO))
        U-nn (le-resp s/zero s/zero pU U (refl s/zero) (sym U pU 'ps-hU) (:nn PU))
        u-le-O (le-resp u u pO O (refl u) (sym O pO 'ps-hO) (:lo PO))
        w-le-U (le-resp w w pU U (refl w) (sym U pU 'ps-hU) (:lo PU))
        goal (eqv (sub O U) u)
        ;; u ~ 0 from u <= 0 and w <= 0
        u-zero (fn [u-np w-np]
                 (anti u s/zero u-np
                       (le-resp (neg s/zero) s/zero (neg w) u (ring (neg s/zero) s/zero) (ring (neg w) u)
                                (call 'signed/negate-reverses-order w s/zero w-np))))
        ;; O - U from the two values
        diff-of (fn [Ov Uv hO hU tail]
                  (a/chain (sub O U) [(sub Ov Uv) (s/add-cong O Ov (neg U) (neg Uv) hO (a/neg-cong U Uv hU))]
                           [u tail]))]
    (s/spec 'signed/positive-part-split
            [['ps-a signed] ['ps-b signed] ['ps-O signed] ['ps-U signed] ['ps-hO (eqv O pO)] ['ps-hU (eqv U pU)]]
            goal
            (cases (eqv pO s/zero) (eqv pO u) goal (:or PO)
                   (f/lam [['ps-o0 (eqv pO s/zero)]]
                          (let [o0 (trans O pO s/zero 'ps-hO 'ps-o0)]
                            (cases (eqv pU s/zero) (eqv pU w) goal (:or PU)
                                   (f/lam [['ps-u0 (eqv pU s/zero)]]
                                          (let [u0 (trans U pU s/zero 'ps-hU 'ps-u0)
                                                uz (u-zero (le-resp u u O s/zero (refl u) o0 u-le-O) (le-resp w w U s/zero (refl w) u0 w-le-U))]
                                            (diff-of s/zero s/zero o0 u0 (trans (sub s/zero s/zero) s/zero u (ring (sub s/zero s/zero) s/zero) (sym u s/zero uz)))))
                                   (f/lam [['ps-uw (eqv pU w)]]
                                          (diff-of s/zero w o0 (trans U pU w 'ps-hU 'ps-uw) (ring (sub s/zero w) u))))))
                   (f/lam [['ps-ou (eqv pO u)]]
                          (let [ou (trans O pO u 'ps-hO 'ps-ou)]
                            (cases (eqv pU s/zero) (eqv pU w) goal (:or PU)
                                   (f/lam [['ps-u0 (eqv pU s/zero)]]
                                          (diff-of u s/zero ou (trans U pU s/zero 'ps-hU 'ps-u0) (ring (sub u s/zero) u)))
                                   (f/lam [['ps-uw (eqv pU w)]]
                                          (let [uw (trans U pU w 'ps-hU 'ps-uw)
                                                ;; 0 <= O ~ u and 0 <= U ~ w: u ~ 0
                                                u-nn (le-resp s/zero s/zero O u (refl s/zero) ou O-nn)
                                                w-nn (le-resp s/zero s/zero U w (refl s/zero) uw U-nn)
                                                u-np (le-resp (neg w) u (neg s/zero) s/zero (ring (neg w) u) (ring (neg s/zero) s/zero)
                                                              (call 'signed/negate-reverses-order s/zero w w-nn))
                                                uz (anti u s/zero u-np u-nn)]
                                            (diff-of u w ou uw
                                                     (a/chain (sub u w) [(add u u) (ring (sub u w) (add u u))]
                                                              [(add s/zero s/zero) (s/add-cong u s/zero u s/zero uz uz)]
                                                              [s/zero (ring (add s/zero s/zero) s/zero)]
                                                              [u (sym u s/zero uz)])))))))))))

(defn pfacts [v w] (pconj (disj (eqv w s/zero) (eqv w v)) (pconj (le s/zero w) (le v w))))

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
  (-> (pdep0/extend-environment checked-environment)
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-nvcost-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
