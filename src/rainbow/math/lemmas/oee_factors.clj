(ns rainbow.math.lemmas.oee-factors
  "General lemmas: oee factors. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn assoc3 [x y z] (call 'signed/multiply-associative x y z))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(def telescope-spec
  (let [[o a p f q r c C G] '[ot-o ot-a ot-p ot-f ot-q ot-r ot-c ot-bigc ot-g]
        fq (mul f q)]
    (s/spec 'signed/oee-telescope
            [['ot-o signed] ['ot-a signed] ['ot-p signed] ['ot-f signed] ['ot-q signed] ['ot-r signed] ['ot-c signed] ['ot-bigc signed] ['ot-g signed]
             ['ot-ho (eqv o (mul a fq))] ['ot-ha (eqv (mul a p) r)] ['ot-hf (eqv (mul f r) (mul c C))] ['ot-hq (eqv (mul q C) G)]]
            (eqv (mul o p) (mul c G))
            (a/chain (mul o p)
                     [(mul (mul a fq) p) (mcong o (mul a fq) p p 'ot-ho (refl p))]
                     [(mul a (mul fq p)) (assoc3 a fq p)]
                     [(mul a (mul p fq)) (mcong a a (mul fq p) (mul p fq) (refl a) (comm fq p))]
                     [(mul (mul a p) fq) (sym (mul (mul a p) fq) (mul a (mul p fq)) (assoc3 a p fq))]
                     [(mul r fq) (mcong (mul a p) r fq fq 'ot-ha (refl fq))]
                     [(mul fq r) (comm r fq)]
                     [(mul (mul q f) r) (mcong fq (mul q f) r r (comm f q) (refl r))]
                     [(mul q (mul f r)) (assoc3 q f r)]
                     [(mul q (mul c C)) (mcong q q (mul f r) (mul c C) (refl q) 'ot-hf)]
                     [(mul (mul q c) C) (sym (mul (mul q c) C) (mul q (mul c C)) (assoc3 q c C))]
                     [(mul (mul c q) C) (mcong (mul q c) (mul c q) C C (comm q c) (refl C))]
                     [(mul c (mul q C)) (assoc3 c q C)]
                     [(mul c G) (mcong c c (mul q C) G (refl c) 'ot-hq)]))))

(def unit-spec
  (let [x 'ru-x d 'ru-d v 'ru-v]
    (s/spec 'signed/ratio-in-unit
            [['ru-x signed] ['ru-d signed] ['ru-v signed] ['ru-pos (lt s/zero d)] ['ru-h (eqv (mul x d) v)]
             ['ru-0 (le s/zero v)] ['ru-1 (le v d)]]
            (pconj (le s/zero x) (le x one))
            (conjoin (le s/zero x) (le x one)
                     (call 'signed/at-most-cancel-positive-right s/zero x d 'ru-pos
                           (le-resp s/zero (mul s/zero d) v (mul x d) (sym (mul s/zero d) s/zero (call 'signed/multiply-zero-left d)) (sym (mul x d) v 'ru-h) 'ru-0))
                     (call 'signed/at-most-cancel-positive-right x one d 'ru-pos
                           (le-resp v (mul x d) d (mul one d) (sym (mul x d) v 'ru-h) (sym (mul one d) d (call 'signed/multiply-one-left d)) 'ru-1))))))

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

(def theorem-specs [telescope-spec unit-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      multiply-associative/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-oee-factors theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
