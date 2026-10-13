(ns rainbow.math.lemmas.pfs-readings
  "General lemmas: pfs readings. The mathematical facts the corresponding checks rest on,
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

(defn max-facts [u v N] (pconj (disj (eqv N u) (eqv N v)) (pconj (le u N) (le v N))))

(def max-clamp-spec
  (let [u 'xc-u v 'xc-v w 'xc-w G 'xc-G N 'xc-N pw (pp w)
        f* (call 'signed/positive-part-cases w)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        rest-t (pconj (le w pw) (disj (eqv pw s/zero) (eqv pw w)))
        sG (sym G pw 'xc-hG)
        G-nn (le-resp s/zero s/zero pw G (refl s/zero) sG (fst (le s/zero pw) rest-t f*))
        w-G (le-resp w w pw G (refl w) sG (fst (le w pw) (disj (eqv pw s/zero) (eqv pw w)) (snd (le s/zero pw) rest-t f*)))
        orr (snd (le w pw) (disj (eqv pw s/zero) (eqv pw w)) (snd (le s/zero pw) rest-t f*))
        uv-G (le-resp w (sub u v) G G 'xc-hw (refl G) w-G)
        sN (sym N (add v G) 'xc-hN)
        v-N (le-resp (add v s/zero) v (add v G) N (ring (add v s/zero) v) sN
                     (le-resp (add s/zero v) (add v s/zero) (add G v) (add v G) (ring (add s/zero v) (add v s/zero)) (ring (add G v) (add v G))
                              (call 'signed/add-right-monotone s/zero G v G-nn)))
        u-N (le-resp (add v (sub u v)) u (add v G) N (ring (add v (sub u v)) u) sN
                     (le-resp (add (sub u v) v) (add v (sub u v)) (add G v) (add v G) (ring (add (sub u v) v) (add v (sub u v))) (ring (add G v) (add v G))
                              (call 'signed/add-right-monotone (sub u v) G v uv-G)))
        N-or (cases (eqv pw s/zero) (eqv pw w) (disj (eqv N u) (eqv N v)) orr
                    (f/lam [['xc-z (eqv pw s/zero)]]
                           (inr (eqv N u) (eqv N v)
                                (a/chain N [(add v G) 'xc-hN] [(add v s/zero) (s/add-cong v v G s/zero (refl v) (trans G pw s/zero 'xc-hG 'xc-z))]
                                         [v (ring (add v s/zero) v)])))
                    (f/lam [['xc-p (eqv pw w)]]
                           (inl (eqv N u) (eqv N v)
                                (a/chain N [(add v G) 'xc-hN]
                                         [(add v (sub u v)) (s/add-cong v v G (sub u v) (refl v) (trans G pw (sub u v) 'xc-hG (trans pw w (sub u v) 'xc-p 'xc-hw)))]
                                         [u (ring (add v (sub u v)) u)]))))]
    (s/spec 'signed/max-by-clamp [['xc-u signed] ['xc-v signed] ['xc-w signed] ['xc-G signed] ['xc-N signed]
                                  ['xc-hw (eqv w (sub u v))] ['xc-hG (eqv G pw)] ['xc-hN (eqv N (add v G))]]
            (max-facts u v N)
            (conjoin (disj (eqv N u) (eqv N v)) (pconj (le u N) (le v N)) N-or
                     (conjoin (le u N) (le v N) u-N v-N)))))

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

(def theorem-specs [max-clamp-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-pfs-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
