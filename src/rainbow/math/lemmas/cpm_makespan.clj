(ns rainbow.math.lemmas.cpm-makespan
  "General lemmas: cpm makespan. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.lemmas.ncyc-infeasible :as ncyc :refer [row-weight potential edge-zero-one row]]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.module :as module]))

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

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn add-r [a b c h] (call 'signed/add-right-monotone a b c h))

(defn add-l [a b c h] (call 'signed/add-left-monotone a b c h))

(def negate-le-spec
  (s/spec 'signed/at-most-negate [['x signed] ['y signed] ['h (le 'x 'y)]]
          (le (neg 'y) (neg 'x))
          (le-resp (add 'x (neg (add 'x 'y))) (neg 'y) (add 'y (neg (add 'x 'y))) (neg 'x)
                   (ring (add 'x (neg (add 'x 'y))) (neg 'y)) (ring (add 'y (neg (add 'x 'y))) (neg 'x))
                   (add-r 'x 'y (neg (add 'x 'y)) 'h))))

(def rearrange-upper-spec
  (s/spec 'signed/cpm-rearrange-upper [['x signed] ['y signed] ['z signed] ['h (le (sub 'x (add 'y 'z)) s/zero)]]
          (le (sub 'x 'y) 'z)
          (le-resp (add (sub 'x (add 'y 'z)) 'z) (sub 'x 'y) (add s/zero 'z) 'z
                   (ring (add (sub 'x (add 'y 'z)) 'z) (sub 'x 'y)) (ring (add s/zero 'z) 'z)
                   (add-r (sub 'x (add 'y 'z)) s/zero 'z 'h))))

(def rearrange-lower-spec
  (s/spec 'signed/cpm-rearrange-lower [['x signed] ['y signed] ['z signed] ['h (le (add 'y 'z) 'x)]]
          (le 'z (sub 'x 'y))
          (le-resp (add (add 'y 'z) (neg 'y)) 'z (add 'x (neg 'y)) (sub 'x 'y)
                   (ring (add (add 'y 'z) (neg 'y)) 'z) (refl (sub 'x 'y))
                   (add-r (add 'y 'z) 'x (neg 'y) 'h))))

(def drop-nonpositive-spec
  (s/spec 'signed/cpm-drop-nonpositive [['a signed] ['b signed] ['c signed] ['h (le (sub 'a 'b) 'c)] ['hb (le 'b s/zero)]]
          (le 'a 'c)
          (le-trans 'a (add 'c 'b) 'c
                    (le-resp (add (sub 'a 'b) 'b) 'a (add 'c 'b) (add 'c 'b) (ring (add (sub 'a 'b) 'b) 'a) (refl (add 'c 'b))
                             (add-r (sub 'a 'b) 'c 'b 'h))
                    (le-resp (add 'c 'b) (add 'c 'b) (add 'c s/zero) 'c (refl (add 'c 'b)) (ring (add 'c s/zero) 'c)
                             (add-l 'b s/zero 'c 'hb)))))

(def drop-nonnegative-spec
  (s/spec 'signed/cpm-drop-nonnegative [['a signed] ['b signed] ['c signed] ['h (le 'c (sub 'a 'b))] ['hb (le s/zero 'b)]]
          (le 'c 'a)
          (le-trans 'c (sub 'a 'b) 'a 'h
                    (le-resp (add (sub 'a 'b) s/zero) (sub 'a 'b) (add (sub 'a 'b) 'b) 'a
                             (ring (add (sub 'a 'b) s/zero) (sub 'a 'b)) (ring (add (sub 'a 'b) 'b) 'a)
                             (add-l s/zero 'b (sub 'a 'b) 'hb)))))

(def sum-negate-spec
  (let [Z (f/lam [['nz nat]] s/zero) NG (f/lam [['ng nat]] (neg (at 'G 'ng))) D (f/lam [['nd nat]] (sub (at Z 'nd) (at 'G 'nd)))]
    (s/spec 'signed/expr-sum-value-negate [['G family] ['n nat]]
            (eqv (sum NG 'n) (neg (sum 'G 'n)))
            (a/chain (sum NG 'n)
                     [(sum D 'n) (a/sum-cong NG D 'n 'na (fn [i _] (ring (neg (at 'G i)) (sub s/zero (at 'G i)))))]
                     [(sub (sum Z 'n) (sum 'G 'n)) (call 'signed/expr-sum-value-subtract Z 'G 'n)]
                     [(sub s/zero (sum 'G 'n)) (s/add-cong (sum Z 'n) s/zero (neg (sum 'G 'n)) (neg (sum 'G 'n)) (call 'signed/expr-sum-value-zero 'n) (refl (neg (sum 'G 'n))))]
                     [(neg (sum 'G 'n)) (ring (sub s/zero (sum 'G 'n)) (neg (sum 'G 'n)))]))))

(defn slack [g h] (f/lam [['mu nat] ['mv nat]] (add (at g 'mv) (add (neg (at g 'mu)) (neg (at h 'mu))))))

(def slack-expand-spec
  (let [a 'a b 'b g 'g h 'h n 'n
        Qa (potential a g n) Qb (potential b g n) Ha (potential a h n)
        k (fn [u] (add (neg (at g u)) (neg (at h u))))
        Sb (sum (f/lam [['sb nat]] (at b 'sb)) n)
        inner (fn [u] (sum (f/lam [['iv nat]] (mul (at b 'iv) (at (slack g h) u 'iv))) n))
        inner-eq (fn [u]
                   (let [F1 (f/lam [['i1 nat]] (mul (at b 'i1) (at g 'i1)))
                         F2 (f/lam [['i2 nat]] (mul (at b 'i2) (k u)))
                         F12 (f/lam [['i3 nat]] (add (at F1 'i3) (at F2 'i3)))]
                     (a/chain (inner u)
                              [(sum F12 n) (a/sum-cong (f/lam [['iv nat]] (mul (at b 'iv) (at (slack g h) u 'iv))) F12 n 'ie
                                                       (fn [v _] (call 'signed/multiply-distributes-add-left (at b v) (at g v) (k u))))]
                              [(add Qb (sum F2 n)) (call 'signed/expr-sum-value-add F1 F2 n)]
                              [(add Qb (mul Sb (k u))) (s/add-cong Qb Qb (sum F2 n) (mul Sb (k u)) (refl Qb)
                                                                   (sym (mul Sb (k u)) (sum F2 n) (call 'signed/expr-sum-value-scale-right (f/lam [['sb nat]] (at b 'sb)) (k u) n)))]
                              [(add Qb (mul one (k u))) (s/add-cong Qb Qb (mul Sb (k u)) (mul one (k u)) (refl Qb) (mcong Sb one (k u) (k u) 'hb1 (refl (k u))))]
                              [(add Qb (k u)) (s/add-cong Qb Qb (mul one (k u)) (k u) (refl Qb) (one-times (k u)))])))
        O (f/lam [['ou nat]] (mul (at a 'ou) (inner 'ou)))
        O1 (f/lam [['o1 nat]] (mul (at a 'o1) Qb))
        O2 (f/lam [['o2 nat]] (mul (at a 'o2) (k 'o2)))
        Z (f/lam [['oz nat]] s/zero)
        AGH (f/lam [['o3 nat]] (add (mul (at a 'o3) (at g 'o3)) (mul (at a 'o3) (at h 'o3))))
        O2' (f/lam [['o4 nat]] (sub (at Z 'o4) (at AGH 'o4)))
        Sa (sum (f/lam [['sa nat]] (at a 'sa)) n)]
    (s/spec 'signed/cpm-slack-expand
            [['a family] ['b family] ['g family] ['h family] ['n nat] ['ha1 (eqv Sa one)] ['hb1 (eqv Sb one)]]
            (eqv (row-weight a b (slack g h) n) (sub Qb (add Qa Ha)))
            (a/chain (sum O n)
                     [(sum (f/lam [['o5 nat]] (add (at O1 'o5) (at O2 'o5))) n)
                      (a/sum-cong O (f/lam [['o5 nat]] (add (at O1 'o5) (at O2 'o5))) n 'oa
                                  (fn [u _] (trans (mul (at a u) (inner u)) (mul (at a u) (add Qb (k u))) (add (mul (at a u) Qb) (mul (at a u) (k u)))
                                                   (mcong (at a u) (at a u) (inner u) (add Qb (k u)) (refl (at a u)) (inner-eq u))
                                                   (call 'signed/multiply-distributes-add-left (at a u) Qb (k u)))))]
                     [(add (sum O1 n) (sum O2 n)) (call 'signed/expr-sum-value-add O1 O2 n)]
                     [(add Qb (sum O2 n))
                      (s/add-cong (sum O1 n) Qb (sum O2 n) (sum O2 n)
                                  (a/chain (sum O1 n) [(mul Sa Qb) (sym (mul Sa Qb) (sum O1 n) (call 'signed/expr-sum-value-scale-right (f/lam [['sa nat]] (at a 'sa)) Qb n))]
                                           [(mul one Qb) (mcong Sa one Qb Qb 'ha1 (refl Qb))] [Qb (one-times Qb)])
                                  (refl (sum O2 n)))]
                     [(add Qb (neg (add Qa Ha)))
                      (s/add-cong Qb Qb (sum O2 n) (neg (add Qa Ha)) (refl Qb)
                                  (a/chain (sum O2 n)
                                           [(sum O2' n) (a/sum-cong O2 O2' n 'ob
                                                                    (fn [u _] (ring (mul (at a u) (k u)) (sub s/zero (add (mul (at a u) (at g u)) (mul (at a u) (at h u)))))))]
                                           [(sub (sum Z n) (sum AGH n)) (call 'signed/expr-sum-value-subtract Z AGH n)]
                                           [(sub s/zero (add Qa Ha))
                                            (s/add-cong (sum Z n) s/zero (neg (sum AGH n)) (neg (add Qa Ha)) (call 'signed/expr-sum-value-zero n)
                                                        (a/neg-cong (sum AGH n) (add Qa Ha)
                                                                    (call 'signed/expr-sum-value-add (f/lam [['q1 nat]] (mul (at a 'q1) (at g 'q1))) (f/lam [['q2 nat]] (mul (at a 'q2) (at h 'q2))) n)))]
                                           [(neg (add Qa Ha)) (ring (sub s/zero (add Qa Ha)) (neg (add Qa Ha)))]))]))))

(defn precedence-premise [E d S n]
  (f/forall [['su nat] ['su-lt (below 'su n)] ['sv nat] ['sv-lt (below 'sv n)] ['se (eqv (at E 'su 'sv) one)]]
            (le (add (at S 'su) (at d 'su)) (at S 'sv))))

(def schedule-step-spec
  (let [a 'a b 'b E 'E d 'd S 'S n 'n
        p (f/lam [['np nat]] (neg (at S 'np)))
        W (f/lam [['wu nat] ['wv nat]] (neg (at d 'wu)))
        Ra (potential a S n) Rb (potential b S n) Da (potential a d n)
        Sb (sum (f/lam [['sb nat]] (at b 'sb)) n)
        hpot (f/lam [['pu nat] ['pu-lt (below 'pu n)] ['pv nat] ['pv-lt (below 'pv n)] ['pe (eqv (at E 'pu 'pv) one)]]
                    (let [Su (at S 'pu) du (at d 'pu) Sv (at S 'pv)]
                      (le-resp (neg Sv) (neg Sv) (neg (add Su du)) (add (neg Su) (neg du)) (refl (neg Sv)) (ring (neg (add Su du)) (add (neg Su) (neg du)))
                               (call 'signed/at-most-negate (add Su du) Sv (at 'hprec 'pu 'pu-lt 'pv 'pv-lt 'pe)))))
        step (call 'signed/one-hot-step-potential-bound a b W E p n 'ha0 'hb0 'ha1 'hb1 'hE 'hstep hpot)
        pot-neg (fn [c] (a/chain (potential c p n)
                                 [(sum (f/lam [['pn nat]] (neg (mul (at c 'pn) (at S 'pn)))) n)
                                  (a/sum-cong (f/lam [['qu nat]] (mul (at c 'qu) (at p 'qu))) (f/lam [['pn nat]] (neg (mul (at c 'pn) (at S 'pn)))) n 'pa
                                              (fn [u _] (call 'signed/multiply-negate-right (at c u) (at S u))))]
                                 [(neg (potential c S n)) (call 'signed/expr-sum-value-negate (f/lam [['qu nat]] (mul (at c 'qu) (at S 'qu))) n)]))
        w-neg (a/chain (row-weight a b W n)
                       [(sum (f/lam [['wn nat]] (neg (mul (at a 'wn) (at d 'wn)))) n)
                        (a/sum-cong (f/lam [['su nat]] (mul (at a 'su) (sum (f/lam [['sv nat]] (mul (at b 'sv) (at W 'su 'sv))) n))) (f/lam [['wn nat]] (neg (mul (at a 'wn) (at d 'wn)))) n 'wa
                                    (fn [u _] (let [nd (neg (at d u))]
                                                (a/chain (mul (at a u) (sum (f/lam [['sv nat]] (mul (at b 'sv) nd)) n))
                                                         [(mul (at a u) (mul Sb nd)) (mcong (at a u) (at a u) (sum (f/lam [['sv nat]] (mul (at b 'sv) nd)) n) (mul Sb nd) (refl (at a u))
                                                                                            (sym (mul Sb nd) (sum (f/lam [['sv nat]] (mul (at b 'sv) nd)) n) (call 'signed/expr-sum-value-scale-right (f/lam [['sb nat]] (at b 'sb)) nd n)))]
                                                         [(mul (at a u) (mul one nd)) (mcong (at a u) (at a u) (mul Sb nd) (mul one nd) (refl (at a u)) (mcong Sb one nd nd 'hb1 (refl nd)))]
                                                         [(mul (at a u) nd) (mcong (at a u) (at a u) (mul one nd) nd (refl (at a u)) (one-times nd))]
                                                         [(neg (mul (at a u) (at d u))) (call 'signed/multiply-negate-right (at a u) (at d u))]))))]
                       [(neg Da) (call 'signed/expr-sum-value-negate (f/lam [['qu nat]] (mul (at a 'qu) (at d 'qu))) n)])
        ;; (-Rb) - (-Ra) <= -Da
        neg-form (le-resp (sub (potential b p n) (potential a p n)) (sub (neg Rb) (neg Ra)) (row-weight a b W n) (neg Da)
                          (s/add-cong (potential b p n) (neg Rb) (neg (potential a p n)) (neg (neg Ra)) (pot-neg b) (a/neg-cong (potential a p n) (neg Ra) (pot-neg a)))
                          w-neg step)]
    (s/spec 'signed/cpm-schedule-step
            [['a family] ['b family] ['E matrix] ['d family] ['S family] ['n nat]
             ['ha0 (s/all-below n #(le s/zero (at a %)))] ['hb0 (s/all-below n #(le s/zero (at b %)))]
             ['ha1 (eqv (sum (f/lam [['sa nat]] (at a 'sa)) n) one)] ['hb1 (eqv Sb one)]
             ['hE (edge-zero-one E n)] ['hstep (eqv (row-weight a b E n) one)]
             ['hprec (precedence-premise E d S n)]]
            (le (add Ra Da) Rb)
            (le-resp (add (sub (neg Rb) (neg Ra)) (add Rb Da)) (add Ra Da) (add (neg Da) (add Rb Da)) Rb
                     (ring (add (sub (neg Rb) (neg Ra)) (add Rb Da)) (add Ra Da)) (ring (add (neg Da) (add Rb Da)) Rb)
                     (add-r (sub (neg Rb) (neg Ra)) (neg Da) (add Rb Da) neg-form)))))

(defn path-binders [P E d ES T n L]
  [['hP0 (all2 'ht (s/succ L) 'hu n #(le s/zero (at P %1 %2)))]
   ['hrow (s/all-below (s/succ L) #(eqv (sum (row P %) n) one))]
   ['hE (edge-zero-one E n)]
   ['hstep (s/all-below L #(eqv (row-weight (row P %) (row P (s/succ %)) E n) one))]
   ['htight (s/all-below L #(le (row-weight (row P %) (row P (s/succ %)) (slack ES d) n) s/zero))]
   ['hstart (le (potential (row P s/nz) ES n) s/zero)]
   ['hend (le T (potential (row P L) (f/lam [['fu nat]] (add (at ES 'fu) (at d 'fu))) n))]])

(defn schedule-binders [E d S C n]
  [['hS0 (s/all-below n #(le s/zero (at S %)))]
   ['hprec (precedence-premise E d S n)]
   ['hfin (s/all-below n #(le (add (at S %) (at d %)) C))]])

(def makespan-spec
  (let [P 'P E 'E d 'd ES 'ES S 'S T 'T C 'C n 'n L 'L
        Q (f/lam [['tq nat]] (potential (row P 'tq) ES n))
        R (f/lam [['tr nat]] (potential (row P 'tr) S n))
        del (f/lam [['td nat]] (potential (row P 'td) d n))
        D (sum del L) dL (at del L)
        row-hyps (fn [t ht]
                   (let [ht1 (s/weaken t L ht) ht2 (call 'nat/successor-monotone (s/succ t) L ht)]
                     {:a0 (f/lam [['w0 nat] ['w0-lt (below 'w0 n)]] (at 'hP0 t ht1 'w0 'w0-lt))
                      :b0 (f/lam [['w1 nat] ['w1-lt (below 'w1 n)]] (at 'hP0 (s/succ t) ht2 'w1 'w1-lt))
                      :a1 (at 'hrow t ht1) :b1 (at 'hrow (s/succ t) ht2)}))
        ;; ES: Q_{t+1} - Q_t <= delta_t
        es-step (fn [t ht]
                  (let [{:keys [a1 b1]} (row-hyps t ht)]
                    (call 'signed/cpm-rearrange-upper (at Q (s/succ t)) (at Q t) (at del t)
                          (le-resp (row-weight (row P t) (row P (s/succ t)) (slack ES d) n) (sub (at Q (s/succ t)) (add (at Q t) (at del t))) s/zero s/zero
                                   (call 'signed/cpm-slack-expand (row P t) (row P (s/succ t)) ES d n a1 b1) (refl s/zero)
                                   (at 'htight t ht)))))
        ;; S: delta_t <= R_{t+1} - R_t
        s-step (fn [t ht]
                 (let [{:keys [a0 b0 a1 b1]} (row-hyps t ht)]
                   (call 'signed/cpm-rearrange-lower (at R (s/succ t)) (at R t) (at del t)
                         (call 'signed/cpm-schedule-step (row P t) (row P (s/succ t)) E d S n a0 b0 a1 b1 'hE (at 'hstep t ht) 'hprec))))
        DQ (f/lam [['dq nat]] (sub (at Q (s/succ 'dq)) (at Q 'dq)))
        DR (f/lam [['dr nat]] (sub (at R (s/succ 'dr)) (at R 'dr)))
        q-tele (le-resp (sum DQ L) (sub (at Q L) (at Q s/nz)) D D (call 'signed/expr-sum-value-telescope Q L) (refl D)
                        (a/sum-mono DQ del L 'mq (fn [t ht] (es-step t ht))))
        r-tele (le-resp D D (sum DR L) (sub (at R L) (at R s/nz)) (refl D) (call 'signed/expr-sum-value-telescope R L)
                        (a/sum-mono del DR L 'mr (fn [t ht] (s-step t ht))))
        L-lt (s/self-below L)
        PL (fn [u] (at P L u))
        split (fn [V] (let [F1 (f/lam [['e1 nat]] (mul (at P L 'e1) (at V 'e1))) F2 (f/lam [['e2 nat]] (mul (at P L 'e2) (at d 'e2)))]
                        (a/chain (potential (row P L) (f/lam [['fu nat]] (add (at V 'fu) (at d 'fu))) n)
                                 [(sum (f/lam [['e3 nat]] (add (at F1 'e3) (at F2 'e3))) n)
                                  (a/sum-cong (f/lam [['qu nat]] (mul (at (row P L) 'qu) (at (f/lam [['fu nat]] (add (at V 'fu) (at d 'fu))) 'qu))) (f/lam [['e3 nat]] (add (at F1 'e3) (at F2 'e3))) n 'ea
                                              (fn [u _] (call 'signed/multiply-distributes-add-left (PL u) (at V u) (at d u))))]
                                 [(add (potential (row P L) V n) dL) (call 'signed/expr-sum-value-add F1 F2 n)])))
        QL (at Q L) RL (at R L)
        ;; T <= Q_L + delta_L <= D + delta_L
        t-le (le-trans T (add QL dL) (add D dL)
                       (le-resp T T (potential (row P L) (f/lam [['fu nat]] (add (at ES 'fu) (at d 'fu))) n) (add QL dL) (refl T) (split ES) 'hend)
                       (add-r QL D dL (call 'signed/cpm-drop-nonpositive QL (at Q s/nz) D q-tele 'hstart)))
        ;; D <= R_L (R_0 >= 0)
        r0 (call 'signed/expr-sum-value-nonnegative (f/lam [['r0 nat]] (mul (at P s/nz 'r0) (at S 'r0))) n
                 (f/lam [['rz nat] ['rz-lt (below 'rz n)]]
                        (nonneg-prod (at P s/nz 'rz) (at S 'rz) (at 'hP0 s/nz (call 'nat/successor-monotone s/nz L (f/app (f/const* 'proposition/witness [type-level]) nat (f/lam [['wz nat]] (f/equality type-level nat (call 'algebra/nat-add s/nz 'wz) L)) L (f/app (f/const* 'equality/reflexive [type-level]) nat L))) 'rz 'rz-lt)
                                     (at 'hS0 'rz 'rz-lt))))
        d-le (call 'signed/cpm-drop-nonnegative RL (at R s/nz) D r-tele r0)
        ;; R_L + delta_L <= C
        CS (f/lam [['cc nat]] (mul (at P L 'cc) C))
        fin (le-resp (potential (row P L) (f/lam [['fu nat]] (add (at S 'fu) (at d 'fu))) n) (add RL dL) (sum CS n) C
                     (split S)
                     (a/chain (sum CS n) [(mul (sum (row P L) n) C) (sym (mul (sum (row P L) n) C) (sum CS n) (call 'signed/expr-sum-value-scale-right (row P L) C n))]
                              [(mul one C) (mcong (sum (row P L) n) one C C (at 'hrow L (s/self-below L)) (refl C))] [C (one-times C)])
                     (a/sum-mono (f/lam [['qu nat]] (mul (at (row P L) 'qu) (at (f/lam [['fu nat]] (add (at S 'fu) (at d 'fu))) 'qu))) CS n 'fa
                                 (fn [u hu] (lmono (PL u) (add (at S u) (at d u)) C (at 'hP0 L (s/self-below L) u hu) (at 'hfin u hu)))))]
    (s/spec 'signed/cpm-makespan-lower-bound
            (-> [['P matrix] ['E matrix] ['d family] ['ES family] ['S family] ['T signed] ['C signed] ['n nat] ['L nat]]
                (into (path-binders P E d ES T n L)) (into (schedule-binders E d S C n)))
            (le T C)
            (le-trans T (add D dL) C t-le (le-trans (add D dL) (add RL dL) C (add-r D RL dL d-le) fin)))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec
                     @#'indep/zero-one-upper-spec @#'indep/one-minus-spec @#'indep/subtract-expand-spec
                     ncyc/term-split-spec ncyc/outer-split-spec ncyc/rearrange-spec ncyc/slack-spec ncyc/telescope-spec ncyc/step-spec])

(def theorem-specs [negate-le-spec rearrange-upper-spec rearrange-lower-spec drop-nonpositive-spec drop-nonnegative-spec sum-negate-spec slack-expand-spec schedule-step-spec makespan-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-cpm-makespan borrowed-specs) (support/extend-with-shared :expr-sum-cpm-makespan theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.cpm-makespan))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
