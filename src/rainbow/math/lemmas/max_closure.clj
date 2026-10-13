(ns rainbow.math.lemmas.max-closure
  "General lemmas: max closure. The mathematical facts the corresponding checks rest on,
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
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
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

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn one-of [y h]   ; 1 - y ~ 0  ->  y ~ 1
  (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
           [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero h))]
           [one (ring (sub one s/zero) one)]))

(defn zo-lo [x h] (call 'signed/zero-one-nonnegative x h))

(defn zo-hi [x h] (call 'signed/zero-one-at-most-one x h))

(def arc-term-spec
  (let [a 'a w 'w xi 'xi xj 'xj d (sub xi xj) goal (le (mul w d) s/zero)
        to-zero (fn [h] (le-resp (mul w d) (mul w d) (mul w s/zero) s/zero (refl (mul w d)) (call 'signed/multiply-zero-right w) h))]
    (s/spec 'signed/closure-arc-term
            [['a signed] ['w signed] ['xi signed] ['xj signed]
             ['ha (zero-one a)] ['hw (le s/zero w)] ['hwa (le w (mul a w))] ['hxi (zero-one xi)] ['hxj (zero-one xj)]
             ['hrow (eqv (mul (mul a xi) (sub one xj)) s/zero)]]
            goal
            (cases (eqv a s/zero) (eqv (sub one a) s/zero) goal (call 'signed/multiply-zero-split a (sub one a) 'ha)
                   ;; off an arc: w <= 0 w ~ 0, so w ~ 0
                   (f/lam [['az (eqv a s/zero)]]
                          (let [w0 (anti w s/zero (le-resp w w (mul a w) s/zero (refl w)
                                                           (trans (mul a w) (mul s/zero w) s/zero (mcong a s/zero w w 'az (refl w)) (call 'signed/multiply-zero-left w))
                                                           'hwa)
                                         'hw)]
                            (a/eq-le (mul w d) s/zero (trans (mul w d) (mul s/zero d) s/zero (mcong w s/zero d d w0 (refl d)) (call 'signed/multiply-zero-left d)))))
                   ;; on an arc: xi (1 - xj) ~ 0, so xi <= xj
                   (f/lam [['ao (eqv (sub one a) s/zero)]]
                          (let [a1 (one-of a 'ao)
                                row (a/chain (mul xi (sub one xj))
                                             [(mul (mul one xi) (sub one xj)) (mcong xi (mul one xi) (sub one xj) (sub one xj) (sym (mul one xi) xi (one-times xi)) (refl (sub one xj)))]
                                             [(mul (mul a xi) (sub one xj)) (mcong (mul one xi) (mul a xi) (sub one xj) (sub one xj) (mcong one a xi xi (sym a one a1) (refl xi)) (refl (sub one xj)))]
                                             [s/zero 'hrow])
                                dle (cases (eqv xi s/zero) (eqv (sub one xj) s/zero) (le d s/zero) (call 'signed/multiply-zero-split xi (sub one xj) row)
                                           (f/lam [['xz (eqv xi s/zero)]]
                                                  (le-resp (sub s/zero xj) d s/zero s/zero (s/add-cong s/zero xi (neg xj) (neg xj) (sym xi s/zero 'xz) (refl (neg xj))) (refl s/zero)
                                                           (le-resp (neg xj) (sub s/zero xj) (neg s/zero) s/zero
                                                                    (ring (neg xj) (sub s/zero xj)) (f/const* 'signed/negate-zero [])
                                                                    (call 'signed/at-most-negate s/zero xj (zo-lo xj 'hxj)))))
                                           (f/lam [['xo (eqv (sub one xj) s/zero)]]
                                                  (le-resp (sub xi one) d (sub one one) s/zero
                                                           (s/add-cong xi xi (neg one) (neg xj) (refl xi) (a/neg-cong one xj (sym xj one (one-of xj 'xo))))
                                                           (ring (sub one one) s/zero)
                                                           (call 'signed/add-right-monotone xi one (neg one) (zo-hi xi 'hxi)))))]
                            (to-zero (lmono w d s/zero 'hw dle))))))))

(defn out-sum [W n i] (sum (f/lam [['oj nat]] (at W i 'oj)) n))

(defn in-sum [W n i] (sum (f/lam [['ik nat]] (at W 'ik i)) n))

(defn open-row [A x n i] (sum (f/lam [['rj nat]] (mul (mul (at A i 'rj) (at x i)) (sub one (at x 'rj)))) n))

(defn profit [p x n] (sum (f/lam [['pi nat]] (mul (at p 'pi) (at x 'pi))) n))

(defn closure-binders [A x n]
  [['hx01 (s/all-below n #(zero-one (at x %)))]
   ['hclosed (s/all-below n #(le (open-row A x n %) s/zero))]])

(def weak-duality-spec
  (let [A 'A W 'W p 'p u 'u x 'x n 'n
        U (sum (f/lam [['us nat]] (at u 'us)) n)
        xv #(at x %)
        X01 (fn [i hi] (at 'hx01 i hi))
        ;; per node: p_i x_i <= u_i x_i + (out_i x_i - in_i x_i)
        F (f/lam [['f1 nat]] (mul (at p 'f1) (xv 'f1)))
        G (f/lam [['g1 nat]] (add (mul (at u 'g1) (xv 'g1)) (sub (mul (out-sum W n 'g1) (xv 'g1)) (mul (in-sum W n 'g1) (xv 'g1)))))
        per (fn [i hi]
              (let [ui (at u i) oi (out-sum W n i) ii (in-sum W n i) pi (at p i)
                    pre (le-resp (add (add pi ii) (neg ii)) pi (add (add ui oi) (neg ii)) (add (add ui oi) (neg ii))
                                 (ring (add (add pi ii) (neg ii)) pi) (refl (add (add ui oi) (neg ii)))
                                 (call 'signed/add-right-monotone (add pi ii) (add ui oi) (neg ii) (at 'hdual i hi)))]
                (le-resp (mul pi (xv i)) (mul pi (xv i)) (mul (add (add ui oi) (neg ii)) (xv i)) (add (mul ui (xv i)) (sub (mul oi (xv i)) (mul ii (xv i))))
                         (refl (mul pi (xv i))) (ring (mul (add (add ui oi) (neg ii)) (xv i)) (add (mul ui (xv i)) (sub (mul oi (xv i)) (mul ii (xv i)))))
                         (rmono (xv i) pi (add (add ui oi) (neg ii)) (zo-lo (xv i) (X01 i hi)) pre))))
        UX (f/lam [['ux nat]] (mul (at u 'ux) (xv 'ux)))
        OX (f/lam [['ox nat]] (mul (out-sum W n 'ox) (xv 'ox)))
        IX (f/lam [['ix nat]] (mul (in-sum W n 'ix) (xv 'ix)))
        DX (f/lam [['dx nat]] (sub (at OX 'dx) (at IX 'dx)))
        ;; sum out x - sum in x ~ sum_{i,j} W(i,j)(x_i - x_j)
        T1 (f/lam [['t1 nat]] (sum (f/lam [['t2 nat]] (mul (at W 't1 't2) (xv 't1))) n))
        T2 (f/lam [['t3 nat]] (sum (f/lam [['t4 nat]] (mul (at W 't3 't4) (xv 't4))) n))
        ARC (f/lam [['a1 nat]] (sum (f/lam [['a2 nat]] (mul (at W 'a1 'a2) (sub (xv 'a1) (xv 'a2)))) n))
        out-eq (a/sum-cong OX T1 n 'ca (fn [i _] (call 'signed/expr-sum-value-scale-right (f/lam [['oj nat]] (at W i 'oj)) (xv i) n)))
        in-eq (a/chain (sum IX n)
                       [(sum (f/lam [['i1 nat]] (sum (f/lam [['i2 nat]] (mul (at W 'i2 'i1) (xv 'i1))) n)) n)
                        (a/sum-cong IX (f/lam [['i1 nat]] (sum (f/lam [['i2 nat]] (mul (at W 'i2 'i1) (xv 'i1))) n)) n 'cb
                                    (fn [i _] (call 'signed/expr-sum-value-scale-right (f/lam [['ik nat]] (at W 'ik i)) (xv i) n)))]
                       [(sum T2 n) (call 'signed/expr-sum-value-swap (f/lam [['sa nat] ['sb nat]] (mul (at W 'sb 'sa) (xv 'sa))) n n)])
        arc-eq (a/chain (sub (sum OX n) (sum IX n))
                        [(sub (sum T1 n) (sum T2 n)) (s/add-cong (sum OX n) (sum T1 n) (neg (sum IX n)) (neg (sum T2 n)) out-eq (a/neg-cong (sum IX n) (sum T2 n) in-eq))]
                        [(sum (f/lam [['d1 nat]] (sub (at T1 'd1) (at T2 'd1))) n) (sym (sum (f/lam [['d1 nat]] (sub (at T1 'd1) (at T2 'd1))) n) (sub (sum T1 n) (sum T2 n)) (call 'signed/expr-sum-value-subtract T1 T2 n))]
                        [(sum ARC n) (a/sum-cong (f/lam [['d1 nat]] (sub (at T1 'd1) (at T2 'd1))) ARC n 'cc
                                                 (fn [i _] (a/chain (sub (at T1 i) (at T2 i))
                                                                    [(sum (f/lam [['d2 nat]] (sub (mul (at W i 'd2) (xv i)) (mul (at W i 'd2) (xv 'd2)))) n)
                                                                     (sym (sum (f/lam [['d2 nat]] (sub (mul (at W i 'd2) (xv i)) (mul (at W i 'd2) (xv 'd2)))) n) (sub (at T1 i) (at T2 i))
                                                                          (call 'signed/expr-sum-value-subtract (f/lam [['t2 nat]] (mul (at W i 't2) (xv i))) (f/lam [['t4 nat]] (mul (at W i 't4) (xv 't4))) n))]
                                                                    [(sum (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) n)
                                                                     (a/sum-cong (f/lam [['d2 nat]] (sub (mul (at W i 'd2) (xv i)) (mul (at W i 'd2) (xv 'd2)))) (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) n 'cd
                                                                                 (fn [j _] (sym (mul (at W i j) (sub (xv i) (xv j))) (sub (mul (at W i j) (xv i)) (mul (at W i j) (xv j)))
                                                                                                (call 'signed/multiply-subtract-expand (at W i j) (xv i) (xv j)))))])))])
        ;; each row of the closedness sum is zero term by term
        row-zero (fn [i hi]
                   (let [Tm (f/lam [['rj nat]] (mul (mul (at A i 'rj) (xv i)) (sub one (xv 'rj))))
                         tnn (f/lam [['tn nat] ['tn-lt (below 'tn n)]]
                                    (nonneg-prod (mul (at A i 'tn) (xv i)) (sub one (xv 'tn))
                                                 (nonneg-prod (at A i 'tn) (xv i) (zo-lo (at A i 'tn) (at 'hA i hi 'tn 'tn-lt)) (zo-lo (xv i) (X01 i hi)))
                                                 (call 'signed/one-minus-nonnegative (xv 'tn) (zo-hi (xv 'tn) (X01 'tn 'tn-lt)))))]
                     (call 'signed/expr-sum-value-nonnegative-terms-zero Tm n tnn
                           (anti (sum Tm n) s/zero (at 'hclosed i hi) (call 'signed/expr-sum-value-nonnegative Tm n tnn)))))
        arcs-le (a/sum-mono ARC (f/lam [['z1 nat]] s/zero) n 'ce
                            (fn [i hi] (le-resp (sum (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) n) (sum (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) n)
                                                (sum (f/lam [['z2 nat]] s/zero) n) s/zero (refl (sum (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) n))
                                                (call 'signed/expr-sum-value-zero n)
                                                (a/sum-mono (f/lam [['a2 nat]] (mul (at W i 'a2) (sub (xv i) (xv 'a2)))) (f/lam [['z2 nat]] s/zero) n 'cf
                                                            (fn [j hj] (call 'signed/closure-arc-term (at A i j) (at W i j) (xv i) (xv j)
                                                                             (at 'hA i hi j hj) (at 'hw i hi j hj) (at 'hwA i hi j hj) (X01 i hi) (X01 j hj)
                                                                             (at (row-zero i hi) j hj)))))))
        arcs-nonpos (le-resp (sum ARC n) (sum ARC n) (sum (f/lam [['z1 nat]] s/zero) n) s/zero (refl (sum ARC n)) (call 'signed/expr-sum-value-zero n) arcs-le)
        ux-le (a/sum-mono UX (f/lam [['us nat]] (at u 'us)) n 'cg
                          (fn [i hi] (le-resp (mul (at u i) (xv i)) (mul (at u i) (xv i)) (mul (at u i) one) (at u i) (refl (mul (at u i) (xv i)))
                                              (a/chain (mul (at u i) one) [(mul one (at u i)) (call 'signed/multiply-commutative (at u i) one)] [(at u i) (one-times (at u i))])
                                              (lmono (at u i) (xv i) one (at 'hu i hi) (zo-hi (xv i) (X01 i hi))))))
        g-sum (a/chain (sum G n)
                       [(add (sum UX n) (sum DX n)) (call 'signed/expr-sum-value-add UX DX n)]
                       [(add (sum UX n) (sub (sum OX n) (sum IX n))) (s/add-cong (sum UX n) (sum UX n) (sum DX n) (sub (sum OX n) (sum IX n)) (refl (sum UX n)) (call 'signed/expr-sum-value-subtract OX IX n))]
                       [(add (sum UX n) (sum ARC n)) (s/add-cong (sum UX n) (sum UX n) (sub (sum OX n) (sum IX n)) (sum ARC n) (refl (sum UX n)) arc-eq)])]
    (s/spec 'signed/closure-weak-duality
            (into [['A matrix] ['W matrix] ['p family] ['u family] ['x family] ['n nat]
                   ['hA (all2 'ai n 'aj n #(zero-one (at A %1 %2)))]
                   ['hu (s/all-below n #(le s/zero (at u %)))]
                   ['hw (all2 'wi n 'wj n #(le s/zero (at W %1 %2)))]
                   ['hwA (all2 'vi n 'vj n #(le (at W %1 %2) (mul (at A %1 %2) (at W %1 %2))))]
                   ['hdual (s/all-below n #(le (add (at p %) (in-sum W n %)) (add (at u %) (out-sum W n %))))]]
                  (closure-binders A x n))
            (le (profit p x n) U)
            (le-trans (profit p x n) (sum G n) U (a/sum-mono F G n 'ch per)
                      (le-resp (add (sum UX n) (sum ARC n)) (sum G n) (add U s/zero) U
                               (sym (sum G n) (add (sum UX n) (sum ARC n)) g-sum) (call 'signed/add-zero-right U)
                               (le-trans (add (sum UX n) (sum ARC n)) (add U (sum ARC n)) (add U s/zero)
                                         (call 'signed/add-right-monotone (sum UX n) U (sum ARC n) ux-le)
                                         (call 'signed/add-left-monotone (sum ARC n) s/zero U arcs-nonpos)))))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec indep/zero-one-upper-spec indep/one-minus-spec indep/subtract-expand-spec
                     cpm/negate-le-spec])

(def theorem-specs [arc-term-spec weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-max-closure borrowed-specs) (support/extend-with-shared :expr-sum-max-closure theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.max-closure))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
