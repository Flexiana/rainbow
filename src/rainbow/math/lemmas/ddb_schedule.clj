(ns rainbow.math.lemmas.ddb-schedule
  "General lemmas: ddb schedule. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.minmax :as minmax]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn min-val [l r] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) r l (call 'signed/decide-at-most l r)))

(def min-cases-spec
  (let [l 'mc-l r 'mc-r
        val (fn [t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) r l t))
        goal (fn [t] (disj (eqv (val t) l) (eqv (val t) r)))]
    (s/spec 'signed/min-cases [['mc-l signed] ['mc-r signed]]
            (goal (call 'signed/decide-at-most l r))
            (f/app (f/const* 'data/Bool.rec [prop-level])
                   (f/lam [['mc-b bool]] (goal 'mc-b))
                   (inr (eqv r l) (eqv r r) (refl r))
                   (inl (eqv l l) (eqv l r) (refl l))
                   (call 'signed/decide-at-most l r)))))

(def telescope-spec
  (let [B 'tl-b D 'tl-d n 'tl-n Bt #(at B %)
        q (f/lam [['tq-i nat]] (neg (Bt 'tq-i)))
        G (f/lam [['tg nat]] (sub (at q (s/succ 'tg)) (at q 'tg)))]
    (s/spec 'signed/ddb-telescope
            [['tl-b family] ['tl-d family] ['tl-n nat]
             ['tl-bal (s/all-below n #(eqv (add (Bt (s/succ %)) (at D %)) (Bt %)))]]
            (eqv (sum D n) (sub (Bt s/nz) (Bt n)))
            (a/chain (sum D n)
                     [(sum G n) (a/sum-cong D G n 'tl-c
                                            (fn [t ht] (let [B1 (Bt (s/succ t)) Dt (at D t)]
                                                         (a/chain Dt [(sub (add B1 Dt) B1) (ring Dt (sub (add B1 Dt) B1))]
                                                                  [(sub (Bt t) B1) (s/add-cong (add B1 Dt) (Bt t) (neg B1) (neg B1) (at 'tl-bal t ht) (refl (neg B1)))]
                                                                  [(sub (neg B1) (neg (Bt t))) (ring (sub (Bt t) B1) (sub (neg B1) (neg (Bt t))))]))))]
                     [(sub (neg (Bt n)) (neg (Bt s/nz))) (call 'signed/expr-sum-value-telescope q n)]
                     [(sub (Bt s/nz) (Bt n)) (ring (sub (neg (Bt n)) (neg (Bt s/nz))) (sub (Bt s/nz) (Bt n)))]))))

(def floor-spec
  (let [B 'fl-b D 'fl-d S 'fl-s n 'fl-n Bt #(at B %)
        claim (fn [t] (f/forall [['fl-ht (below t (s/succ n))]] (le S (Bt t))))]
    (s/spec 'signed/ddb-floor-invariant
            [['fl-b family] ['fl-d family] ['fl-s signed] ['fl-n nat]
             ['fl-bal (s/all-below n #(eqv (add (Bt (s/succ %)) (at D %)) (Bt %)))]
             ['fl-room (s/all-below n #(le (at D %) (sub (Bt %) S)))]
             ['fl-0 (le S (Bt s/nz))]
             ['fl-t nat]]
            (claim 'fl-t)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['fl-k nat]] (claim 'fl-k))
                   (f/lam [['fl-ht (below s/nz (s/succ n))]] 'fl-0)
                   (f/lam [['fl-j nat] ['fl-ih (claim 'fl-j)] ['fl-ht (below (s/succ 'fl-j) (s/succ n))]]
                          (let [j 'fl-j Bj (Bt j) B1 (Bt (s/succ j)) Dj (at D j)
                                hj (call 'nat/at-most-of-successor-at-most (s/succ j) n 'fl-ht)
                                prev (at 'fl-ih (call 'nat/strict-below-weaken j n hj))
                                ;; D_j <= B_j - S  ->  S <= B_j - D_j ~ B_{j+1}
                                shifted (call 'signed/add-right-monotone Dj (sub Bj S) (sub S Dj) (at 'fl-room j hj))
                                B1-eq (a/chain (sub Bj Dj)
                                               [(sub (add B1 Dj) Dj) (s/add-cong Bj (add B1 Dj) (neg Dj) (neg Dj) (sym (add B1 Dj) Bj (at 'fl-bal j hj)) (refl (neg Dj)))]
                                               [B1 (ring (sub (add B1 Dj) Dj) B1)])]
                            (le-resp (add Dj (sub S Dj)) S (add (sub Bj S) (sub S Dj)) B1
                                     (ring (add Dj (sub S Dj)) S)
                                     (trans (add (sub Bj S) (sub S Dj)) (sub Bj Dj) B1 (ring (add (sub Bj S) (sub S Dj)) (sub Bj Dj)) B1-eq)
                                     shifted)))
                   'fl-t))))

(defn reading [D l r] (pconj (le D l) (pconj (le D r) (disj (eqv D l) (eqv D r)))))

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

(def theorem-specs [min-cases-spec telescope-spec floor-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      minmax/extend-environment
      nat-more/extend-environment
      add-monotone/extend-environment
      (support/extend-with-shared :expr-sum-ddb-schedule theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
