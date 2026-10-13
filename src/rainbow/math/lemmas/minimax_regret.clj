(ns rainbow.math.lemmas.minimax-regret
  "General lemmas: minimax regret. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center :refer [le-ind eq-ind]]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(defn witnessed [I c x] (disj (eqv I s/zero) (pconj (eqv I one) (le c x))))

(def witness-bound-spec
  (let [I 'I F 'F c 'c R 'R n 'n
        SI (sum (f/lam [['si nat]] (at I 'si)) n)
        I-nn (fn [i hi] (cases (eqv (at I i) s/zero) (pconj (eqv (at I i) one) (le c (at F i))) (le s/zero (at I i)) (at 'hI i hi)
                               (f/lam [['nz (eqv (at I i) s/zero)]] (a/eq-le s/zero (at I i) (sym (at I i) s/zero 'nz)))
                               (f/lam [['no (pconj (eqv (at I i) one) (le c (at F i)))]]
                                      (le-resp s/zero s/zero one (at I i) (refl s/zero) (sym (at I i) one (pleft (eqv (at I i) one) (le c (at F i)) 'no)) zero-le-one))))
        per-i (fn [i hi]
                (let [Ii (at I i) goal (le (mul Ii c) (mul Ii R))]
                  (cases (eqv Ii s/zero) (pconj (eqv Ii one) (le c (at F i))) goal (at 'hI i hi)
                         (f/lam [['pz (eqv Ii s/zero)]]
                                (a/eq-le (mul Ii c) (mul Ii R)
                                         (a/chain (mul Ii c) [(mul s/zero c) (mcong Ii s/zero c c 'pz (refl c))] [s/zero (call 'signed/multiply-zero-left c)]
                                                  [(mul s/zero R) (sym (mul s/zero R) s/zero (call 'signed/multiply-zero-left R))]
                                                  [(mul Ii R) (mcong s/zero Ii R R (sym Ii s/zero 'pz) (refl R))])))
                         (f/lam [['po (pconj (eqv Ii one) (le c (at F i)))]]
                                (le-trans (mul Ii c) (mul Ii (at F i)) (mul Ii R)
                                          (lmono Ii c (at F i) (I-nn i hi) (pright (eqv Ii one) (le c (at F i)) 'po))
                                          (lmono Ii (at F i) R (I-nn i hi) (at 'hb i hi)))))))
        IC (f/lam [['ic nat]] (mul (at I 'ic) c)) IR (f/lam [['ir nat]] (mul (at I 'ir) R))
        summed (le-resp (sum IC n) (mul c SI) (sum IR n) (mul R SI)
                        (a/chain (sum IC n) [(mul SI c) (sym (mul SI c) (sum IC n) (call 'signed/expr-sum-value-scale-right (f/lam [['si nat]] (at I 'si)) c n))]
                                 [(mul c SI) (call 'signed/multiply-commutative SI c)])
                        (a/chain (sum IR n) [(mul SI R) (sym (mul SI R) (sum IR n) (call 'signed/expr-sum-value-scale-right (f/lam [['si nat]] (at I 'si)) R n))]
                                 [(mul R SI) (call 'signed/multiply-commutative SI R)])
                        (a/sum-mono IC IR n 'wm (fn [i hi] (per-i i hi))))]
    (s/spec 'signed/indicator-witness-bound
            [['I family] ['F family] ['c signed] ['R signed] ['n nat]
             ['hI (s/all-below n #(witnessed (at I %) c (at F %)))]
             ['hsum (le one SI)]
             ['hb (s/all-below n #(le (at F %) R))]]
            (le c R)
            (call 'signed/at-most-cancel-positive-right c R SI
                  (call 'signed/less-than-of-less-than-of-at-most s/zero one SI (f/const* 'signed/zero-less-than-one []) 'hsum)
                  summed))))

(defn chosen [U w m s] (sum (f/lam [['ca nat]] (mul (at w 'ca) (at U 'ca s))) m))

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

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "regret-conditions-" stem)) :accepted (symbol "signed" (str "regret-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-regret-" stem))} kind))

(def borrowed-specs [center/le-indicator-cases-spec center/eq-indicator-cases-spec center/attained-bound-spec])

(def theorem-specs [witness-bound-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      (support/extend-with-shared :expr-sum-minimax-regret theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
