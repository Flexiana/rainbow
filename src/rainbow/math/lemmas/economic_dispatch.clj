(ns rainbow.math.lemmas.economic-dispatch
  "General lemmas: economic dispatch. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn add-l [a b c h] (call 'signed/add-left-monotone a b c h))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn nonneg-add [x y hx hy]
  (le-resp (add s/zero s/zero) s/zero (add x y) (add x y) (call 'signed/add-zero-right s/zero) (refl (add x y))
           (le-trans (add s/zero s/zero) (add x s/zero) (add x y) (call 'signed/add-right-monotone s/zero x s/zero hx) (add-l s/zero y x hy))))

(def two center/two)

(defn cost [b c x] (add (mul b x) (mul c (mul x x))))

(defn marginal [b c p mp mm] (add (add (add b (mul (mul two c) p)) mp) (neg mm)))

(def nonneg-diff-spec
  (s/spec 'signed/nonneg-minus-nonpositive [['y signed] ['x signed] ['hy (le s/zero 'y)] ['hx (le 'x s/zero)]]
          (le s/zero (sub 'y 'x))
          (le-resp (add s/zero s/zero) s/zero (add 'y (neg 'x)) (sub 'y 'x) (call 'signed/add-zero-right s/zero) (refl (sub 'y 'x))
                   (le-trans (add s/zero s/zero) (add 'y s/zero) (add 'y (neg 'x)) (call 'signed/add-right-monotone s/zero 'y s/zero 'hy)
                             (add-l s/zero (neg 'x) 'y
                                    (le-resp (neg s/zero) s/zero (neg 'x) (neg 'x) (f/const* 'signed/negate-zero []) (refl (neg 'x))
                                             (call 'signed/at-most-negate 'x s/zero 'hx)))))))

(defn dist-r [x y z] (call 'signed/multiply-distributes-add-right x y z))

(def square-shift-spec
  (let [c 'c p 'p q 'q d (sub q p) pd (mul p d)
        steps (a/chain (add (mul c (mul d d)) (mul (mul (add c c) p) d))
                       [(add (mul c (mul d d)) (mul (add c c) pd))
                        (s/add-cong (mul c (mul d d)) (mul c (mul d d)) (mul (mul (add c c) p) d) (mul (add c c) pd) (refl (mul c (mul d d)))
                                    (call 'signed/multiply-associative (add c c) p d))]
                       [(add (mul c (mul d d)) (add (mul c pd) (mul c pd)))
                        (s/add-cong (mul c (mul d d)) (mul c (mul d d)) (mul (add c c) pd) (add (mul c pd) (mul c pd)) (refl (mul c (mul d d)))
                                    (call 'signed/multiply-distributes-add-right c c pd))]
                       [(add (mul c (mul d d)) (mul c (add pd pd)))
                        (s/add-cong (mul c (mul d d)) (mul c (mul d d)) (add (mul c pd) (mul c pd)) (mul c (add pd pd)) (refl (mul c (mul d d)))
                                    (sym (mul c (add pd pd)) (add (mul c pd) (mul c pd)) (call 'signed/multiply-distributes-add-left c pd pd)))]
                       [(mul c (add (mul d d) (add pd pd)))
                        (sym (mul c (add (mul d d) (add pd pd))) (add (mul c (mul d d)) (mul c (add pd pd))) (call 'signed/multiply-distributes-add-left c (mul d d) (add pd pd)))]
                       [(mul c (sub (mul q q) (mul p p)))
                        (mcong c c (add (mul d d) (add pd pd)) (sub (mul q q) (mul p p)) (refl c) (ring (add (mul d d) (add pd pd)) (sub (mul q q) (mul p p))))]
                       [(sub (mul c (mul q q)) (mul c (mul p p))) (call 'signed/multiply-subtract-expand c (mul q q) (mul p p))])]
    (s/spec 'signed/dispatch-square-shift [['c signed] ['p signed] ['q signed]]
            (eqv (add (mul c (mul d d)) (mul (mul (add c c) p) d)) (sub (mul c (mul q q)) (mul c (mul p p))))
            steps)))

(def assemble-spec
  (let [vs '[bp cpp bd xd mpd mmd sq cqq bq]
        [bp cpp bd xd mpd mmd sq cqq bq] vs
        lhs (add (add (add bp cpp) (add (add (add bd xd) mpd) (neg mmd))) (add sq (add (neg mpd) mmd)))
        mid (add (add bp bd) (add (add sq xd) cpp))]
    (s/spec 'signed/dispatch-assemble
            (into (mapv (fn [v] [v signed]) vs) [['h1 (eqv (add bp bd) bq)] ['h2 (eqv (add sq xd) (sub cqq cpp))]])
            (eqv lhs (add bq cqq))
            (a/chain lhs [mid (ring lhs mid)]
                     [(add bq (add (sub cqq cpp) cpp)) (s/add-cong (add bp bd) bq (add (add sq xd) cpp) (add (sub cqq cpp) cpp) 'h1
                                                                   (s/add-cong (add sq xd) (sub cqq cpp) cpp cpp 'h2 (refl cpp)))]
                     [(add bq cqq) (ring (add bq (add (sub cqq cpp) cpp)) (add bq cqq))]))))

(def term-spec
  (let [b 'b c 'c p 'p q 'q l 'l mp 'mp mm 'mm lo 'lo hi 'hi
        d (sub q p)
        X (mul (add c c) p)
        Mp (add (add (add b X) mp) (neg mm))
        sq (mul c (mul d d))
        up (sub (mul mp (sub hi q)) (mul mp (sub hi p)))
        dn (sub (mul mm (sub q lo)) (mul mm (sub p lo)))
        K (add sq (add up dn))
        sq-nn (nonneg-prod c (mul d d) 'hc (call 'signed/zero-at-most-of-nonnegative (mul d d) (call 'signed/square-nonnegative d)))
        up-nn (call 'signed/nonneg-minus-nonpositive (mul mp (sub hi q)) (mul mp (sub hi p))
                    (nonneg-prod mp (sub hi q) 'hmp (le-resp (sub q q) s/zero (sub hi q) (sub hi q) (ring (sub q q) s/zero) (refl (sub hi q))
                                                             (call 'signed/add-right-monotone q hi (neg q) 'hqhi)))
                    'hup)
        dn-nn (call 'signed/nonneg-minus-nonpositive (mul mm (sub q lo)) (mul mm (sub p lo))
                    (nonneg-prod mm (sub q lo) 'hmm (le-resp (sub lo lo) s/zero (sub q lo) (sub q lo) (ring (sub lo lo) s/zero) (refl (sub q lo))
                                                             (call 'signed/add-right-monotone lo q (neg lo) 'hloq)))
                    'hlow)
        K-nn (nonneg-add sq (add up dn) sq-nn (nonneg-add up dn up-nn dn-nn))
        lM (a/chain l [(marginal b c p mp mm) (sym (marginal b c p mp mm) l 'hstat)]
                    [Mp (s/add-cong (add (add b (mul (mul two c) p)) mp) (add (add b X) mp) (neg mm) (neg mm)
                                    (s/add-cong (add b (mul (mul two c) p)) (add b X) mp mp
                                                (s/add-cong b b (mul (mul two c) p) X (refl b)
                                                            (mcong (mul two c) (add c c) p p (call 'signed/two-times c) (refl p)))
                                                (refl mp))
                                    (refl (neg mm)))])
        ;; (Mp) d ~ ((b d + X d) + mp d) + -(mm d), by distributivity (no ring)
        A1 (add (add b X) mp)
        E1 (a/chain (mul Mp d)
                    [(add (mul A1 d) (mul (neg mm) d)) (dist-r A1 (neg mm) d)]
                    [(add (add (mul (add b X) d) (mul mp d)) (mul (neg mm) d))
                     (s/add-cong (mul A1 d) (add (mul (add b X) d) (mul mp d)) (mul (neg mm) d) (mul (neg mm) d) (dist-r (add b X) mp d) (refl (mul (neg mm) d)))]
                    [(add (add (add (mul b d) (mul X d)) (mul mp d)) (mul (neg mm) d))
                     (s/add-cong (add (mul (add b X) d) (mul mp d)) (add (add (mul b d) (mul X d)) (mul mp d)) (mul (neg mm) d) (mul (neg mm) d)
                                 (s/add-cong (mul (add b X) d) (add (mul b d) (mul X d)) (mul mp d) (mul mp d) (dist-r b X d) (refl (mul mp d)))
                                 (refl (mul (neg mm) d)))]
                    [(add (add (add (mul b d) (mul X d)) (mul mp d)) (neg (mul mm d)))
                     (s/add-cong (add (add (mul b d) (mul X d)) (mul mp d)) (add (add (mul b d) (mul X d)) (mul mp d)) (mul (neg mm) d) (neg (mul mm d))
                                 (refl (add (add (mul b d) (mul X d)) (mul mp d))) (call 'signed/multiply-negate-left mm d))])
        ;; the complementarity blocks are -(mp d) and mm d (degree-2 rings)
        e-up (ring up (neg (mul mp d)))
        e-dn (ring dn (mul mm d))
        bp (mul b p) cpp (mul c (mul p p)) bd (mul b d) xd (mul X d) mpd (mul mp d) mmd (mul mm d) cqq (mul c (mul q q)) bq (mul b q)
        cost-p (cost b c p)
        base (add cost-p (mul l d))
        base' (add cost-p (mul Mp d))
        lhs-blocks (add (add (add bp cpp) (add (add (add bd xd) mpd) (neg mmd))) (add sq (add (neg mpd) mmd)))
        to-blocks (s/add-cong base' (add (add bp cpp) (add (add (add bd xd) mpd) (neg mmd))) K (add sq (add (neg mpd) mmd))
                              (s/add-cong cost-p (add bp cpp) (mul Mp d) (add (add (add bd xd) mpd) (neg mmd)) (refl cost-p) E1)
                              (s/add-cong sq sq (add up dn) (add (neg mpd) mmd) (refl sq) (s/add-cong up (neg mpd) dn mmd e-up e-dn)))
        ident (trans (add base' K) lhs-blocks (cost b c q) to-blocks
                     (call 'signed/dispatch-assemble bp cpp bd xd mpd mmd sq cqq bq
                           (ring (add bp bd) bq)
                           (call 'signed/dispatch-square-shift c p q)))]
    (s/spec 'signed/dispatch-term-bound
            [['b signed] ['c signed] ['p signed] ['q signed] ['l signed] ['mp signed] ['mm signed] ['lo signed] ['hi signed]
             ['hc (le s/zero 'c)] ['hmp (le s/zero 'mp)] ['hmm (le s/zero 'mm)]
             ['hstat (eqv (marginal b c p mp mm) l)] ['hup (le (mul mp (sub hi p)) s/zero)] ['hlow (le (mul mm (sub p lo)) s/zero)]
             ['hloq (le lo q)] ['hqhi (le q hi)]]
            (le base (cost b c q))
            (le-resp (add base s/zero) base (add base K) (cost b c q)
                     (call 'signed/add-zero-right base)
                     (trans (add base K) (add base' K) (cost b c q)
                            (s/add-cong base base' K K (s/add-cong cost-p cost-p (mul l d) (mul Mp d) (refl cost-p) (mcong l Mp d d lM (refl d))) (refl K))
                            ident)
                     (call 'signed/add-left-monotone s/zero K base K-nn)))))

(defn total-cost [b c x n] (sum (f/lam [['tc nat]] (cost (at b 'tc) (at c 'tc) (at x 'tc))) n))

(defn tsum [x n] (sum (f/lam [['ts nat]] (at x 'ts)) n))

(def optimal-spec
  (let [b 'b c 'c p 'p q 'q mp 'mp mm 'mm lo 'lo hi 'hi l 'l D 'D n 'n
        Base (f/lam [['ob nat]] (add (cost (at b 'ob) (at c 'ob) (at p 'ob)) (mul l (sub (at q 'ob) (at p 'ob)))))
        CP (f/lam [['oc nat]] (cost (at b 'oc) (at c 'oc) (at p 'oc)))
        LD (f/lam [['ol nat]] (mul l (sub (at q 'ol) (at p 'ol))))
        DQ (f/lam [['od nat]] (sub (at q 'od) (at p 'od)))
        ld-zero (a/chain (sum LD n)
                         [(mul l (sum DQ n)) (sym (mul l (sum DQ n)) (sum LD n) (call 'signed/expr-sum-value-scale-left DQ l n))]
                         [(mul l (sub (tsum q n) (tsum p n))) (mcong l l (sum DQ n) (sub (tsum q n) (tsum p n)) (refl l) (call 'signed/expr-sum-value-subtract q p n))]
                         [(mul l (sub D D)) (mcong l l (sub (tsum q n) (tsum p n)) (sub D D) (refl l) (s/add-cong (tsum q n) D (neg (tsum p n)) (neg D) 'hqD (a/neg-cong (tsum p n) D 'hpD)))]
                         [(mul l s/zero) (mcong l l (sub D D) s/zero (refl l) (ring (sub D D) s/zero))]
                         [s/zero (call 'signed/multiply-zero-right l)])
        base-sum (a/chain (sum Base n)
                          [(add (sum CP n) (sum LD n)) (call 'signed/expr-sum-value-add CP LD n)]
                          [(add (sum CP n) s/zero) (s/add-cong (sum CP n) (sum CP n) (sum LD n) s/zero (refl (sum CP n)) ld-zero)]
                          [(sum CP n) (call 'signed/add-zero-right (sum CP n))])]
    (s/spec 'signed/dispatch-cost-optimal
            [['b family] ['c family] ['p family] ['q family] ['mp family] ['mm family] ['lo family] ['hi family] ['l signed] ['D signed] ['n nat]
             ['hc (s/all-below n #(le s/zero (at c %)))] ['hmp (s/all-below n #(le s/zero (at mp %)))] ['hmm (s/all-below n #(le s/zero (at mm %)))]
             ['hpD (eqv (tsum p n) D)]
             ['hstat (s/all-below n #(eqv (marginal (at b %) (at c %) (at p %) (at mp %) (at mm %)) l))]
             ['hup (s/all-below n #(le (mul (at mp %) (sub (at hi %) (at p %))) s/zero))]
             ['hlow (s/all-below n #(le (mul (at mm %) (sub (at p %) (at lo %))) s/zero))]
             ['hqD (eqv (tsum q n) D)] ['hloq (s/all-below n #(le (at lo %) (at q %)))] ['hqhi (s/all-below n #(le (at q %) (at hi %)))]]
            (le (total-cost b c p n) (total-cost b c q n))
            (le-resp (sum Base n) (total-cost b c p n) (total-cost b c q n) (total-cost b c q n) base-sum (refl (total-cost b c q n))
                     (a/sum-mono Base (f/lam [['tc nat]] (cost (at b 'tc) (at c 'tc) (at q 'tc))) n 'om
                                 (fn [i ib] (call 'signed/dispatch-term-bound (at b i) (at c i) (at p i) (at q i) l (at mp i) (at mm i) (at lo i) (at hi i)
                                                  (at 'hc i ib) (at 'hmp i ib) (at 'hmm i ib) (at 'hstat i ib) (at 'hup i ib) (at 'hlow i ib)
                                                  (at 'hloq i ib) (at 'hqhi i ib))))))))

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

(def theorem-specs [nonneg-diff-spec square-shift-spec assemble-spec term-spec optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      dot-negate/extend-environment
      norm-nn/extend-environment
      multiply-associative/extend-environment
      (support/extend-with-shared :expr-sum-economic-dispatch theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
