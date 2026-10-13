(ns rainbow.math.lemmas.one-center
  "General lemmas: one center. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn add-r [a b c h] (call 'signed/add-right-monotone a b c h))

(defn add-l [a b c h] (call 'signed/add-left-monotone a b c h))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(defn le-ind [p q]
  (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) s/zero one (call 'signed/decide-at-most p q)))

(defn eq-ind [p c] (mul (le-ind p c) (le-ind c p)))

(defn picked [I x c] (disj (eqv I s/zero) (pconj (eqv I one) (eqv x c))))

(def le-indicator-cases-spec
  (let [D (call 'signed/decide-at-most 'p 'q)
        sel (fn [t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) s/zero one t))
        goal (fn [t] (disj (eqv (sel t) s/zero) (pconj (eqv (sel t) one) (le 'p 'q))))
        eqb (fn [t] (f/equality type-level bool D t))]
    (s/spec 'signed/le-indicator-cases [['p signed] ['q signed]]
            (goal D)
            (f/app (f/const* 'data/Bool.rec [prop-level])
                   (f/lam [['lb bool]] (f/forall [['lh (eqb 'lb)]] (goal 'lb)))
                   (f/lam [['lh (eqb (f/const* 'data/false []))]]
                          (inl (eqv s/zero s/zero) (pconj (eqv s/zero one) (le 'p 'q)) (refl s/zero)))
                   (f/lam [['lh (eqb (f/const* 'data/true []))]]
                          (inr (eqv one s/zero) (pconj (eqv one one) (le 'p 'q))
                               (conjoin (eqv one one) (le 'p 'q) (refl one) (call 'signed/decide-at-most-true-sound 'p 'q 'lh))))
                   D
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(def eq-indicator-cases-spec
  (let [L1 (le-ind 'p 'c) L2 (le-ind 'c 'p) I (mul L1 L2) goal (picked I 'p 'c)
        zero-left (fn [h] (inl (eqv I s/zero) (pconj (eqv I one) (eqv 'p 'c))
                               (a/chain I [(mul s/zero L2) (mcong L1 s/zero L2 L2 h (refl L2))] [s/zero (call 'signed/multiply-zero-left L2)])))]
    (s/spec 'signed/eq-indicator-cases [['p signed] ['c signed]]
            goal
            (cases (eqv L1 s/zero) (pconj (eqv L1 one) (le 'p 'c)) goal (call 'signed/le-indicator-cases 'p 'c)
                   (f/lam [['e1z (eqv L1 s/zero)]] (zero-left 'e1z))
                   (f/lam [['e1o (pconj (eqv L1 one) (le 'p 'c))]]
                          (let [l1 (pleft (eqv L1 one) (le 'p 'c) 'e1o) pc (pright (eqv L1 one) (le 'p 'c) 'e1o)]
                            (cases (eqv L2 s/zero) (pconj (eqv L2 one) (le 'c 'p)) goal (call 'signed/le-indicator-cases 'c 'p)
                                   (f/lam [['e2z (eqv L2 s/zero)]]
                                          (inl (eqv I s/zero) (pconj (eqv I one) (eqv 'p 'c))
                                               (a/chain I [(mul L1 s/zero) (mcong L1 L1 L2 s/zero (refl L1) 'e2z)] [s/zero (call 'signed/multiply-zero-right L1)])))
                                   (f/lam [['e2o (pconj (eqv L2 one) (le 'c 'p))]]
                                          (let [l2 (pleft (eqv L2 one) (le 'c 'p) 'e2o) cp (pright (eqv L2 one) (le 'c 'p) 'e2o)]
                                            (inr (eqv I s/zero) (pconj (eqv I one) (eqv 'p 'c))
                                                 (conjoin (eqv I one) (eqv 'p 'c)
                                                          (a/chain I [(mul one one) (mcong L1 one L2 one l1 l2)] [one (one-times one)])
                                                          (call 'signed/at-most-antisymmetric 'p 'c pc cp))))))))))))

(def attained-bound-spec
  (let [I 'I F 'F c 'c R 'R n 'n
        SI (sum (f/lam [['si nat]] (at I 'si)) n)
        I-nn (fn [i hi] (cases (eqv (at I i) s/zero) (pconj (eqv (at I i) one) (eqv (at F i) c)) (le s/zero (at I i)) (at 'hI i hi)
                               (f/lam [['nz (eqv (at I i) s/zero)]] (a/eq-le s/zero (at I i) (sym (at I i) s/zero 'nz)))
                               (f/lam [['no (pconj (eqv (at I i) one) (eqv (at F i) c))]]
                                      (le-resp s/zero s/zero one (at I i) (refl s/zero) (sym (at I i) one (pleft (eqv (at I i) one) (eqv (at F i) c) 'no)) zero-le-one))))
        per-i (fn [i hi]
                (let [Ii (at I i) goal (le (mul Ii c) (mul Ii R))]
                  (cases (eqv Ii s/zero) (pconj (eqv Ii one) (eqv (at F i) c)) goal (at 'hI i hi)
                         (f/lam [['pz (eqv Ii s/zero)]]
                                (a/eq-le (mul Ii c) (mul Ii R)
                                         (a/chain (mul Ii c) [(mul s/zero c) (mcong Ii s/zero c c 'pz (refl c))] [s/zero (call 'signed/multiply-zero-left c)]
                                                  [(mul s/zero R) (sym (mul s/zero R) s/zero (call 'signed/multiply-zero-left R))]
                                                  [(mul Ii R) (mcong s/zero Ii R R (sym Ii s/zero 'pz) (refl R))])))
                         (f/lam [['po (pconj (eqv Ii one) (eqv (at F i) c))]]
                                (le-resp (mul Ii (at F i)) (mul Ii c) (mul Ii R) (mul Ii R)
                                         (mcong Ii Ii (at F i) c (refl Ii) (pright (eqv Ii one) (eqv (at F i) c) 'po)) (refl (mul Ii R))
                                         (lmono Ii (at F i) R (I-nn i hi) (at 'hb i hi)))))))
        IC (f/lam [['ic nat]] (mul (at I 'ic) c)) IR (f/lam [['ir nat]] (mul (at I 'ir) R))
        summed (le-resp (sum IC n) (mul c SI) (sum IR n) (mul R SI)
                        (a/chain (sum IC n) [(mul SI c) (sym (mul SI c) (sum IC n) (call 'signed/expr-sum-value-scale-right (f/lam [['si nat]] (at I 'si)) c n))]
                                 [(mul c SI) (call 'signed/multiply-commutative SI c)])
                        (a/chain (sum IR n) [(mul SI R) (sym (mul SI R) (sum IR n) (call 'signed/expr-sum-value-scale-right (f/lam [['si nat]] (at I 'si)) R n))]
                                 [(mul R SI) (call 'signed/multiply-commutative SI R)])
                        (a/sum-mono IC IR n 'am (fn [i hi] (per-i i hi))))]
    (s/spec 'signed/indicator-attained-bound
            [['I family] ['F family] ['c signed] ['R signed] ['n nat]
             ['hI (s/all-below n #(picked (at I %) (at F %) c))]
             ['hsum (le one SI)]
             ['hb (s/all-below n #(le (at F %) R))]]
            (le c R)
            (call 'signed/at-most-cancel-positive-right c R SI
                  (call 'signed/less-than-of-less-than-of-at-most s/zero one SI (f/const* 'signed/zero-less-than-one []) 'hsum)
                  summed))))

(def two-times-spec
  (let [o1 (of-nat/of-nat (s/succ s/nz))
        ;; of-nat 1 = from-nnrat (make 1 0) is signed/one by unfolding (reflexivity)
        two-eq (a/chain two [(add o1 one) (call 'signed/of-nat-successor (s/succ s/nz))]
                        [(add one one) (s/add-cong o1 one one one (refl one) (refl one))])]
    (s/spec 'signed/two-times [['x signed]]
            (eqv (mul two 'x) (add 'x 'x))
            (a/chain (mul two 'x) [(mul (add one one) 'x) (mcong two (add one one) 'x 'x two-eq (refl 'x))]
                     [(add (mul one 'x) (mul one 'x)) (call 'signed/multiply-distributes-add-right one one 'x)]
                     [(add 'x 'x) (s/add-cong (mul one 'x) 'x (mul one 'x) 'x (one-times 'x) (one-times 'x))]))))

(def halve-spec
  (s/spec 'signed/at-most-halve [['u signed] ['v signed] ['h (le (add 'u 'u) (add 'v 'v))]]
          (le 'u 'v)
          (call 'signed/at-most-cancel-positive-right 'u 'v two (call 'signed/of-nat-successor-positive (s/succ s/nz))
                (le-resp (add 'u 'u) (mul 'u two) (add 'v 'v) (mul 'v two)
                         (sym (mul 'u two) (add 'u 'u) (trans (mul 'u two) (mul two 'u) (add 'u 'u) (call 'signed/multiply-commutative 'u two) (call 'signed/two-times 'u)))
                         (sym (mul 'v two) (add 'v 'v) (trans (mul 'v two) (mul two 'v) (add 'v 'v) (call 'signed/multiply-commutative 'v two) (call 'signed/two-times 'v)))
                         'h))))

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

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(def covers-spec
  (let [ai 'ai x 'x r 'r lo 'lo hi 'hi lo-a 'lo-a a-hi 'a-hi rr 'rr xx 'xx
        ;; (a - x) + (a - x) ~ (a + a) - (lo + hi) <= (hi + hi) - (lo + hi) ~ hi - lo ~ r + r
        up (le-resp (sub (add ai ai) (add lo hi)) (add (sub ai x) (sub ai x)) (sub (add hi hi) (add lo hi)) (add r r)
                    (a/chain (sub (add ai ai) (add lo hi))
                             [(sub (add ai ai) (add x x)) (s/add-cong (add ai ai) (add ai ai) (neg (add lo hi)) (neg (add x x)) (refl (add ai ai)) (a/neg-cong (add lo hi) (add x x) (sym (add x x) (add lo hi) xx)))]
                             [(add (sub ai x) (sub ai x)) (ring (sub (add ai ai) (add x x)) (add (sub ai x) (sub ai x)))])
                    (a/chain (sub (add hi hi) (add lo hi)) [(sub hi lo) (ring (sub (add hi hi) (add lo hi)) (sub hi lo))] [(add r r) (sym (add r r) (sub hi lo) rr)])
                    (add-r (add ai ai) (add hi hi) (neg (add lo hi)) (le-trans (add ai ai) (add hi ai) (add hi hi) (add-r ai hi ai a-hi) (add-l ai hi hi a-hi))))
        ;; (x - a) + (x - a) ~ (lo + hi) - (a + a) <= (lo + hi) - (lo + lo) ~ hi - lo ~ r + r
        down (le-resp (sub (add lo hi) (add ai ai)) (add (sub x ai) (sub x ai)) (sub (add lo hi) (add lo lo)) (add r r)
                      (a/chain (sub (add lo hi) (add ai ai))
                               [(sub (add x x) (add ai ai)) (s/add-cong (add lo hi) (add x x) (neg (add ai ai)) (neg (add ai ai)) (sym (add x x) (add lo hi) xx) (refl (neg (add ai ai))))]
                               [(add (sub x ai) (sub x ai)) (ring (sub (add x x) (add ai ai)) (add (sub x ai) (sub x ai)))])
                      (a/chain (sub (add lo hi) (add lo lo)) [(sub hi lo) (ring (sub (add lo hi) (add lo lo)) (sub hi lo))] [(add r r) (sym (add r r) (sub hi lo) rr)])
                      (add-l (neg (add ai ai)) (neg (add lo lo)) (add lo hi)
                             (call 'signed/at-most-negate (add lo lo) (add ai ai) (le-trans (add lo lo) (add ai lo) (add ai ai) (add-r lo ai lo lo-a) (add-l lo ai ai lo-a)))))]
    (s/spec 'signed/interval-midpoint-covers
            [['ai signed] ['x signed] ['r signed] ['lo signed] ['hi signed]
             ['lo-a (le lo ai)] ['a-hi (le ai hi)] ['xx (eqv (add x x) (add lo hi))] ['rr (eqv (add r r) (sub hi lo))]]
            (pconj (le (sub ai x) r) (le (sub x ai) r))
            (conjoin (le (sub ai x) r) (le (sub x ai) r)
                     (call 'signed/at-most-halve (sub ai x) r up)
                     (call 'signed/at-most-halve (sub x ai) r down)))))

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "center-conditions-" stem)) :accepted (symbol "signed" (str "center-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-center-" stem))} kind))

(def borrowed-specs [indep/total-spec mmck/cancel-or-zero-spec mmck/cancel-positive-spec mmck/successor-positive-spec
                     pcmax/cancel-order-spec cpm/negate-le-spec])

(def theorem-specs [le-indicator-cases-spec eq-indicator-cases-spec attained-bound-spec two-times-spec halve-spec covers-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      dot-negate/extend-environment
      of-nat/extend-environment
      (support/extend-with-shared :expr-sum-one-center theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
