(ns rainbow.math.lemmas.ncyc-infeasible
  "General lemmas: ncyc infeasible. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
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

(def prop-level [:zero])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn assoc3 [x y z] (call 'signed/multiply-associative x y z))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn scale-left [F c n] (call 'signed/expr-sum-value-scale-left F c n))

(defn scale-right [F c n] (call 'signed/expr-sum-value-scale-right F c n))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(def term-split-spec
  (s/spec 'signed/ncyc-term-split [['b signed] ['w signed] ['pu signed] ['pv signed]]
          (eqv (mul 'b (add 'w (sub 'pu 'pv))) (add (mul 'b 'w) (sub (mul 'pu 'b) (mul 'b 'pv))))
          (ring (mul 'b (add 'w (sub 'pu 'pv))) (add (mul 'b 'w) (sub (mul 'pu 'b) (mul 'b 'pv))))))

(def outer-split-spec
  (s/spec 'signed/ncyc-outer-split [['a signed] ['w signed] ['pu signed] ['qb signed]]
          (eqv (mul 'a (add 'w (sub 'pu 'qb))) (add (mul 'a 'w) (sub (mul 'a 'pu) (mul 'a 'qb))))
          (ring (mul 'a (add 'w (sub 'pu 'qb))) (add (mul 'a 'w) (sub (mul 'a 'pu) (mul 'a 'qb))))))

(def rearrange-spec
  (s/spec 'signed/ncyc-rearrange [['w signed] ['qa signed] ['qb signed] ['h (le s/zero (add 'w (sub 'qa 'qb)))]]
          (le (sub 'qb 'qa) 'w)
          (le-resp (add s/zero (sub 'qb 'qa)) (sub 'qb 'qa) (add (add 'w (sub 'qa 'qb)) (sub 'qb 'qa)) 'w
                   (ring (add s/zero (sub 'qb 'qa)) (sub 'qb 'qa))
                   (ring (add (add 'w (sub 'qa 'qb)) (sub 'qb 'qa)) 'w)
                   (call 'signed/add-right-monotone s/zero (add 'w (sub 'qa 'qb)) (sub 'qb 'qa) 'h))))

(def slack-spec
  (s/spec 'signed/ncyc-edge-slack [['pu signed] ['pv signed] ['w signed] ['h (le 'pv (add 'pu 'w))]]
          (le s/zero (add 'w (sub 'pu 'pv)))
          (le-resp (add 'pv (neg 'pv)) s/zero (add (add 'pu 'w) (neg 'pv)) (add 'w (sub 'pu 'pv))
                   (ring (add 'pv (neg 'pv)) s/zero) (ring (add (add 'pu 'w) (neg 'pv)) (add 'w (sub 'pu 'pv)))
                   (call 'signed/add-right-monotone 'pv (add 'pu 'w) (neg 'pv) 'h))))

(def telescope-spec
  (let [D (f/lam [['tq nat]] (sub (at 'q (s/succ 'tq)) (at 'q 'tq)))
        claim (fn [k] (eqv (sum D k) (sub (at 'q k) (at 'q s/nz))))]
    (s/spec 'signed/expr-sum-value-telescope [['q family] ['L nat]]
            (claim 'L)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['tel-k nat]] (claim 'tel-k))
                   (ring s/zero (sub (at 'q s/nz) (at 'q s/nz)))
                   (f/lam [['tel-j nat] ['tel-ih (claim 'tel-j)]]
                          (let [j 'tel-j qj (at 'q j) q1 (at 'q (s/succ j)) q0 (at 'q s/nz)]
                            (a/chain (add (sum D j) (sub q1 qj))
                                     [(add (sub qj q0) (sub q1 qj)) (s/add-cong (sum D j) (sub qj q0) (sub q1 qj) (sub q1 qj) 'tel-ih (refl (sub q1 qj)))]
                                     [(sub q1 q0) (ring (add (sub qj q0) (sub q1 qj)) (sub q1 q0))])))
                   'L))))

(defn row-weight [a b M n]                    ; sum_u a_u (sum_v b_v M(u,v)) -- the checker's step form
  (sum (f/lam [['su nat]] (mul (at a 'su) (sum (f/lam [['sv nat]] (mul (at b 'sv) (at M 'su 'sv))) n))) n))

(defn potential [a p n] (sum (f/lam [['qu nat]] (mul (at a 'qu) (at p 'qu))) n))

(defn potential-premise [W E p n]
  (f/forall [['pu nat] ['pu-lt (below 'pu n)] ['pv nat] ['pv-lt (below 'pv n)] ['pe (eqv (at E 'pu 'pv) one)]]
            (le (at p 'pv) (add (at p 'pu) (at W 'pu 'pv)))))

(defn edge-zero-one [E n] (all2 'eu n 'ev n #(eqv (mul (at E %1 %2) (sub one (at E %1 %2))) s/zero)))

(def step-spec
  (let [av #(at 'a %) bv #(at 'b %) W #(at 'W %1 %2) E #(at 'E %1 %2) pv #(at 'p %)
        G (fn [u v] (add (W u v) (sub (pv u) (pv v))))
        c (fn [u v] (sub one (E u v)))
        Kf (fn [u] (f/lam [['kv nat]] (mul (bv 'kv) (c u 'kv))))
        K (fn [u] (sum (Kf u) 'n))
        Bf (fn [u] (f/lam [['bv2 nat]] (mul (bv 'bv2) (E u 'bv2))))
        B (fn [u] (sum (Bf u) 'n))
        Sa (sum (f/lam [['sa nat]] (av 'sa)) 'n) Sb (sum (f/lam [['sb nat]] (bv 'sb)) 'n)
        qa (potential 'a 'p 'n) qb (potential 'b 'p 'n)
        w (row-weight 'a 'b 'W 'n)
        e-upper (fn [u v hu hv] (call 'signed/zero-one-at-most-one (E u v) (at 'hE u hu v hv)))
        ;; K u ~ 1 - B u, each term of K >= 0
        K-eq (fn [u]
               (let [F (f/lam [['kf nat]] (bv 'kf)) Gb (Bf u)]
                 (a/chain (K u)
                          [(sum (f/lam [['kd nat]] (sub (bv 'kd) (mul (bv 'kd) (E u 'kd)))) 'n)
                           (a/sum-cong (Kf u) (f/lam [['kd nat]] (sub (bv 'kd) (mul (bv 'kd) (E u 'kd)))) 'n 'kc
                                       (fn [v _] (a/chain (mul (bv v) (c u v))
                                                          [(sub (mul (bv v) one) (mul (bv v) (E u v))) (call 'signed/multiply-subtract-expand (bv v) one (E u v))]
                                                          [(sub (bv v) (mul (bv v) (E u v)))
                                                           (s/add-cong (mul (bv v) one) (bv v) (neg (mul (bv v) (E u v))) (neg (mul (bv v) (E u v)))
                                                                       (times-one (bv v)) (refl (neg (mul (bv v) (E u v)))))])))]
                          [(sub Sb (B u)) (call 'signed/expr-sum-value-subtract F Gb 'n)]
                          [(sub one (B u)) (s/add-cong Sb one (neg (B u)) (neg (B u)) 'hb1 (refl (neg (B u))))])))
        K-nonneg (fn [u hu]
                   (call 'signed/expr-sum-value-nonnegative (Kf u) 'n
                         (f/lam [['kn nat] ['kn-lt (below 'kn 'n)]]
                                (nonneg-prod (bv 'kn) (c u 'kn) (at 'hb0 'kn 'kn-lt)
                                             (call 'signed/one-minus-nonnegative (E u 'kn) (e-upper u 'kn hu 'kn-lt))))))
        Df (f/lam [['du nat]] (mul (av 'du) (K 'du)))
        D-zero (a/chain (sum Df 'n)
                        [(sum (f/lam [['dd nat]] (sub (av 'dd) (mul (av 'dd) (B 'dd)))) 'n)
                         (a/sum-cong Df (f/lam [['dd nat]] (sub (av 'dd) (mul (av 'dd) (B 'dd)))) 'n 'dc
                                     (fn [u _] (a/chain (mul (av u) (K u))
                                                        [(mul (av u) (sub one (B u))) (mcong (av u) (av u) (K u) (sub one (B u)) (refl (av u)) (K-eq u))]
                                                        [(sub (mul (av u) one) (mul (av u) (B u))) (call 'signed/multiply-subtract-expand (av u) one (B u))]
                                                        [(sub (av u) (mul (av u) (B u)))
                                                         (s/add-cong (mul (av u) one) (av u) (neg (mul (av u) (B u))) (neg (mul (av u) (B u)))
                                                                     (times-one (av u)) (refl (neg (mul (av u) (B u)))))])))]
                        [(sub Sa (row-weight 'a 'b 'E 'n))
                         (call 'signed/expr-sum-value-subtract (f/lam [['dg nat]] (av 'dg)) (f/lam [['dh nat]] (mul (av 'dh) (B 'dh))) 'n)]
                        [(sub one one) (s/add-cong Sa one (neg (row-weight 'a 'b 'E 'n)) (neg one) 'ha1 (a/neg-cong (row-weight 'a 'b 'E 'n) one 'hstep))]
                        [s/zero (ring (sub one one) s/zero)])
        D-terms (f/lam [['dt nat] ['dt-lt (below 'dt 'n)]]
                       (nonneg-prod (av 'dt) (K 'dt) (at 'ha0 'dt 'dt-lt) (K-nonneg 'dt 'dt-lt)))
        outer-zero (call 'signed/expr-sum-value-nonnegative-terms-zero Df 'n D-terms D-zero)
        ;; a_u (b_v (1 - E)) ~ 0
        Z (fn [u v hu hv]
            (let [Zf (f/lam [['zf nat]] (mul (av u) (mul (bv 'zf) (c u 'zf))))
                  inner-zero (trans (sum Zf 'n) (mul (av u) (K u)) s/zero
                                    (sym (mul (av u) (K u)) (sum Zf 'n) (scale-left (Kf u) (av u) 'n))
                                    (at outer-zero u hu))
                  inner-terms (f/lam [['zt nat] ['zt-lt (below 'zt 'n)]]
                                     (nonneg-prod (av u) (mul (bv 'zt) (c u 'zt)) (at 'ha0 u hu)
                                                  (nonneg-prod (bv 'zt) (c u 'zt) (at 'hb0 'zt 'zt-lt)
                                                               (call 'signed/one-minus-nonnegative (E u 'zt) (e-upper u 'zt hu 'zt-lt)))))]
              (at (call 'signed/expr-sum-value-nonnegative-terms-zero Zf 'n inner-terms inner-zero) v hv)))
        ;; 0 <= a_u (b_v G(u,v))
        T (fn [u v] (mul (av u) (mul (bv v) (G u v))))
        T-nonneg
        (fn [u v hu hv]
          (let [e (E u v) goal (le s/zero (T u v))]
            (cases (eqv e s/zero) (eqv (sub one e) s/zero) goal
                   (call 'signed/multiply-zero-split e (sub one e) (at 'hE u hu v hv))
                   (f/lam [['ez (eqv e s/zero)]]
                          (let [c1 (a/chain (sub one e) [(sub one s/zero) (s/add-cong one one (neg e) (neg s/zero) (refl one) (a/neg-cong e s/zero 'ez))]
                                            [one (ring (sub one s/zero) one)])
                                ab (mul (av u) (bv v))
                                ab0 (a/chain ab
                                             [(mul (av u) (mul (bv v) one)) (mcong (av u) (av u) (bv v) (mul (bv v) one) (refl (av u)) (sym (mul (bv v) one) (bv v) (times-one (bv v))))]
                                             [(mul (av u) (mul (bv v) (sub one e)))
                                              (mcong (av u) (av u) (mul (bv v) one) (mul (bv v) (sub one e)) (refl (av u))
                                                     (mcong (bv v) (bv v) one (sub one e) (refl (bv v)) (sym (sub one e) one c1)))]
                                             [s/zero (Z u v hu hv)])
                                t0 (a/chain (T u v)
                                            [(mul ab (G u v)) (sym (mul ab (G u v)) (T u v) (assoc3 (av u) (bv v) (G u v)))]
                                            [(mul s/zero (G u v)) (mcong ab s/zero (G u v) (G u v) ab0 (refl (G u v)))]
                                            [s/zero (call 'signed/multiply-zero-left (G u v))])]
                            (a/eq-le s/zero (T u v) (sym (T u v) s/zero t0))))
                   (f/lam [['e1 (eqv (sub one e) s/zero)]]
                          (let [eo (a/chain e [(sub one (sub one e)) (ring e (sub one (sub one e)))]
                                            [(sub one s/zero) (s/add-cong one one (neg (sub one e)) (neg s/zero) (refl one) (a/neg-cong (sub one e) s/zero 'e1))]
                                            [one (ring (sub one s/zero) one)])
                                slack (call 'signed/ncyc-edge-slack (pv u) (pv v) (W u v) (at 'hpot u hu v hv eo))]
                            (nonneg-prod (av u) (mul (bv v) (G u v)) (at 'ha0 u hu)
                                         (nonneg-prod (bv v) (G u v) (at 'hb0 v hv) slack)))))))
        Tf (fn [u] (f/lam [['tv nat]] (mul (bv 'tv) (G u 'tv))))
        inner-G (fn [u] (sum (Tf u) 'n))
        Of (f/lam [['ou nat]] (mul (av 'ou) (inner-G 'ou)))
        outer-nonneg (call 'signed/expr-sum-value-nonnegative Of 'n
                           (f/lam [['on nat] ['on-lt (below 'on 'n)]]
                                  (le-resp s/zero s/zero (sum (f/lam [['ot nat]] (T 'on 'ot)) 'n) (mul (av 'on) (inner-G 'on))
                                           (refl s/zero) (sym (mul (av 'on) (inner-G 'on)) (sum (f/lam [['ot nat]] (T 'on 'ot)) 'n)
                                                              (scale-left (Tf 'on) (av 'on) 'n))
                                           (call 'signed/expr-sum-value-nonnegative (f/lam [['ot nat]] (T 'on 'ot)) 'n
                                                 (f/lam [['oi nat] ['oi-lt (below 'oi 'n)]] (T-nonneg 'on 'oi 'on-lt 'oi-lt))))))
        ;; inner-G u ~ w-inner u + (p_u - qb)
        w-inner (fn [u] (sum (f/lam [['wv nat]] (mul (bv 'wv) (W u 'wv))) 'n))
        inner-eq
        (fn [u]
          (let [F1 (f/lam [['i1 nat]] (mul (bv 'i1) (W u 'i1)))
                F2 (f/lam [['i2 nat]] (sub (mul (pv u) (bv 'i2)) (mul (bv 'i2) (pv 'i2))))
                P1 (f/lam [['i3 nat]] (mul (pv u) (bv 'i3)))
                P2 (f/lam [['i4 nat]] (mul (bv 'i4) (pv 'i4)))
                Fb (f/lam [['i5 nat]] (bv 'i5))
                pu-sum (a/chain (sum P1 'n)
                                [(mul (pv u) Sb) (sym (mul (pv u) Sb) (sum P1 'n) (scale-left Fb (pv u) 'n))]
                                [(mul (pv u) one) (mcong (pv u) (pv u) Sb one (refl (pv u)) 'hb1)]
                                [(pv u) (times-one (pv u))])]
            (a/chain (inner-G u)
                     [(sum (f/lam [['i6 nat]] (add (at F1 'i6) (at F2 'i6))) 'n)
                      (a/sum-cong (Tf u) (f/lam [['i6 nat]] (add (at F1 'i6) (at F2 'i6))) 'n 'ic
                                  (fn [v _] (call 'signed/ncyc-term-split (bv v) (W u v) (pv u) (pv v))))]
                     [(add (w-inner u) (sum F2 'n)) (call 'signed/expr-sum-value-add F1 F2 'n)]
                     [(add (w-inner u) (sub (sum P1 'n) qb))
                      (s/add-cong (w-inner u) (w-inner u) (sum F2 'n) (sub (sum P1 'n) qb) (refl (w-inner u))
                                  (call 'signed/expr-sum-value-subtract P1 P2 'n))]
                     [(add (w-inner u) (sub (pv u) qb))
                      (s/add-cong (w-inner u) (w-inner u) (sub (sum P1 'n) qb) (sub (pv u) qb) (refl (w-inner u))
                                  (s/add-cong (sum P1 'n) (pv u) (neg qb) (neg qb) pu-sum (refl (neg qb))))])))
        outer-eq
        (let [Wf (f/lam [['o1 nat]] (mul (av 'o1) (w-inner 'o1)))
              R (f/lam [['o2 nat]] (sub (mul (av 'o2) (pv 'o2)) (mul (av 'o2) qb)))
              A1 (f/lam [['o3 nat]] (mul (av 'o3) (pv 'o3)))
              A2 (f/lam [['o4 nat]] (mul (av 'o4) qb))
              Fa (f/lam [['o5 nat]] (av 'o5))
              aq (a/chain (sum A2 'n)
                          [(mul Sa qb) (sym (mul Sa qb) (sum A2 'n) (scale-right Fa qb 'n))]
                          [(mul one qb) (mcong Sa one qb qb 'ha1 (refl qb))]
                          [qb (one-times qb)])]
          (a/chain (sum Of 'n)
                   [(sum (f/lam [['o6 nat]] (add (at Wf 'o6) (at R 'o6))) 'n)
                    (a/sum-cong Of (f/lam [['o6 nat]] (add (at Wf 'o6) (at R 'o6))) 'n 'oc
                                (fn [u _] (a/chain (mul (av u) (inner-G u))
                                                   [(mul (av u) (add (w-inner u) (sub (pv u) qb))) (mcong (av u) (av u) (inner-G u) (add (w-inner u) (sub (pv u) qb)) (refl (av u)) (inner-eq u))]
                                                   [(add (mul (av u) (w-inner u)) (sub (mul (av u) (pv u)) (mul (av u) qb)))
                                                    (call 'signed/ncyc-outer-split (av u) (w-inner u) (pv u) qb)])))]
                   [(add w (sum R 'n)) (call 'signed/expr-sum-value-add Wf R 'n)]
                   [(add w (sub qa (sum A2 'n))) (s/add-cong w w (sum R 'n) (sub qa (sum A2 'n)) (refl w) (call 'signed/expr-sum-value-subtract A1 A2 'n))]
                   [(add w (sub qa qb)) (s/add-cong w w (sub qa (sum A2 'n)) (sub qa qb) (refl w)
                                                    (s/add-cong qa qa (neg (sum A2 'n)) (neg qb) (refl qa) (a/neg-cong (sum A2 'n) qb aq)))]))]
    (s/spec 'signed/one-hot-step-potential-bound
            [['a family] ['b family] ['W matrix] ['E matrix] ['p family] ['n nat]
             ['ha0 (s/all-below 'n #(le s/zero (at 'a %)))] ['hb0 (s/all-below 'n #(le s/zero (at 'b %)))]
             ['ha1 (eqv Sa one)] ['hb1 (eqv Sb one)]
             ['hE (edge-zero-one 'E 'n)] ['hstep (eqv (row-weight 'a 'b 'E 'n) one)]
             ['hpot (potential-premise 'W 'E 'p 'n)]]
            (le (sub qb qa) w)
            (call 'signed/ncyc-rearrange w qa qb
                  (le-resp s/zero s/zero (sum Of 'n) (add w (sub qa qb)) (refl s/zero) outer-eq outer-nonneg)))))

(defn row [P t] (f/lam [['rw nat]] (at P t 'rw)))

(defn walk-total [P W n L] (sum (f/lam [['wt nat]] (row-weight (row P 'wt) (row P (s/succ 'wt)) W n)) L))

(def walk-spec
  (let [q (f/lam [['wq nat]] (potential (row 'P 'wq) 'p 'n))
        step-hyps
        (fn [t ht]                                  ; t < L
          (let [ht1 (s/weaken t 'L ht)                                          ; t < L + 1
                ht2 (call 'nat/successor-monotone (s/succ t) 'L ht)]            ; t + 1 < L + 1
            (call 'signed/one-hot-step-potential-bound (row 'P t) (row 'P (s/succ t)) 'W 'E 'p 'n
                  (f/lam [['w0 nat] ['w0-lt (below 'w0 'n)]] (at 'hP0 t ht1 'w0 'w0-lt))
                  (f/lam [['w1 nat] ['w1-lt (below 'w1 'n)]] (at 'hP0 (s/succ t) ht2 'w1 'w1-lt))
                  (at 'hrow t ht1) (at 'hrow (s/succ t) ht2) 'hE (at 'hstep t ht) 'hpot)))
        D (f/lam [['dq nat]] (sub (at q (s/succ 'dq)) (at q 'dq)))
        Wt (f/lam [['wt nat]] (row-weight (row 'P 'wt) (row 'P (s/succ 'wt)) 'W 'n))
        closed (a/sum-cong (f/lam [['cu nat]] (mul (at 'P 'L 'cu) (at 'p 'cu))) (f/lam [['cu nat]] (mul (at 'P s/nz 'cu) (at 'p 'cu))) 'n 'cc
                           (fn [u hu] (mcong (at 'P 'L u) (at 'P s/nz u) (at 'p u) (at 'p u) (at 'hclose u hu) (refl (at 'p u)))))
        zero-sum (a/chain (sum D 'L)
                          [(sub (at q 'L) (at q s/nz)) (call 'signed/expr-sum-value-telescope q 'L)]
                          [(sub (at q s/nz) (at q s/nz)) (s/add-cong (at q 'L) (at q s/nz) (neg (at q s/nz)) (neg (at q s/nz)) closed (refl (neg (at q s/nz))))]
                          [s/zero (ring (sub (at q s/nz) (at q s/nz)) s/zero)])]
    (s/spec 'signed/closed-walk-potential-nonnegative
            [['P matrix] ['W matrix] ['E matrix] ['p family] ['n nat] ['L nat]
             ['hP0 (all2 'ht (s/succ 'L) 'hu 'n #(le s/zero (at 'P %1 %2)))]
             ['hrow (s/all-below (s/succ 'L) #(eqv (sum (row 'P %) 'n) one))]
             ['hclose (s/all-below 'n #(eqv (at 'P 'L %) (at 'P s/nz %)))]
             ['hE (edge-zero-one 'E 'n)]
             ['hstep (s/all-below 'L #(eqv (row-weight (row 'P %) (row 'P (s/succ %)) 'E 'n) one))]
             ['hpot (potential-premise 'W 'E 'p 'n)]]
            (le s/zero (walk-total 'P 'W 'n 'L))
            (le-resp (sum D 'L) s/zero (sum Wt 'L) (walk-total 'P 'W 'n 'L) zero-sum (refl (sum Wt 'L))
                     (a/sum-mono D Wt 'L 'st (fn [t ht] (step-hyps t ht)))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec
                     @#'indep/zero-one-upper-spec @#'indep/one-minus-spec @#'indep/subtract-expand-spec])

(def theorem-specs [term-split-spec outer-split-spec rearrange-spec slack-spec telescope-spec step-spec walk-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.indep-set-dual rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-ncyc-infeasible borrowed-specs) (support/extend-with-shared :expr-sum-ncyc-infeasible theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.ncyc-infeasible))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
