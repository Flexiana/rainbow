(ns rainbow.math.lemmas.pcmax-lower-bound
  "General lemmas: pcmax lower bound. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
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

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn lt [x y] (call 'signed/less-than x y))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn load [Y p n i] (sum (f/lam [['lj nat]] (mul (at Y i 'lj) (at p 'lj))) n))

(defn column [Y m j] (sum (f/lam [['ci nat]] (at Y 'ci j)) m))

(defn competitor-binders [Y p Cp m n]
  [['hY01 (all2 'yi m 'yj n #(zero-one (at Y %1 %2)))]
   ['hcol (s/all-below n #(eqv (column Y m %) one))]
   ['hload (s/all-below m #(le (load Y p n %) Cp))]])

(defn y-lo [Y i j hi hj] (call 'signed/zero-one-nonnegative (at Y i j) (at 'hY01 i hi j hj)))

(defn spread [Y p m j hj]
  (let [F (f/lam [['sf nat]] (at Y 'sf j))]
    (a/chain (at p j)
             [(mul one (at p j)) (sym (mul one (at p j)) (at p j) (one-times (at p j)))]
             [(mul (column Y m j) (at p j)) (mcong one (column Y m j) (at p j) (at p j) (sym (column Y m j) one (at 'hcol j hj)) (refl (at p j)))]
             [(sum (f/lam [['sg nat]] (mul (at Y 'sg j) (at p j))) m) (call 'signed/expr-sum-value-scale-right F (at p j) m)])))

(def job-bound-spec
  (let [Y 'Y p 'p m 'm n 'n Cp 'Cp j 'j
        Fj (f/lam [['jf nat]] (mul (at Y 'jf j) (at p j)))
        Gj (f/lam [['jg nat]] (mul (at Y 'jg j) (load Y p n 'jg)))
        Hj (f/lam [['jh nat]] (mul (at Y 'jh j) Cp))
        per-i (fn [i hi]
                ;; Y p_j <= Y L_i: Y ~ 0 makes both 0; Y ~ 1 turns Y L_i into L_i >= Y p_j
                (let [y (at Y i j) Li (load Y p n i) goal (le (mul y (at p j)) (mul y Li))
                      term (call 'signed/expr-sum-value-term-bound (f/lam [['tk nat]] (mul (at Y i 'tk) (at p 'tk))) n
                                 (f/lam [['tn nat] ['tn-lt (below 'tn n)]] (nonneg-prod (at Y i 'tn) (at p 'tn) (y-lo Y i 'tn hi 'tn-lt) (at 'hp 'tn 'tn-lt)))
                                 j 'j-lt)]
                  (cases (eqv y s/zero) (eqv (sub one y) s/zero) goal
                         (call 'signed/multiply-zero-split y (sub one y) (at 'hY01 i hi j 'j-lt))
                         (f/lam [['yz (eqv y s/zero)]]
                                (a/eq-le (mul y (at p j)) (mul y Li)
                                         (a/chain (mul y (at p j))
                                                  [(mul s/zero (at p j)) (mcong y s/zero (at p j) (at p j) 'yz (refl (at p j)))]
                                                  [s/zero (call 'signed/multiply-zero-left (at p j))]
                                                  [(mul s/zero Li) (sym (mul s/zero Li) s/zero (call 'signed/multiply-zero-left Li))]
                                                  [(mul y Li) (mcong s/zero y Li Li (sym y s/zero 'yz) (refl Li))])))
                         (f/lam [['y1 (eqv (sub one y) s/zero)]]
                                (let [yo (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
                                                  [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero 'y1))]
                                                  [one (ring (sub one s/zero) one)])]
                                  (le-resp (mul y (at p j)) (mul y (at p j)) Li (mul y Li) (refl (mul y (at p j)))
                                           (a/chain Li [(mul one Li) (sym (mul one Li) Li (one-times Li))]
                                                    [(mul y Li) (mcong one y Li Li (sym y one yo) (refl Li))])
                                           term))))))]
    (s/spec 'signed/pcmax-job-bound
            (into [['Y matrix] ['p family] ['Cp signed] ['m nat] ['n nat]]
                  (into (competitor-binders Y p Cp m n)
                        [['hp (s/all-below n #(le s/zero (at p %)))] ['j nat] ['j-lt (below 'j n)]]))
            (le (at p j) Cp)
            (le-resp (sum Fj m) (at p j) (sum Hj m) Cp
                     (sym (at p j) (sum Fj m) (spread Y p m j 'j-lt))
                     (a/chain (sum Hj m)
                              [(mul (column Y m j) Cp) (sym (mul (column Y m j) Cp) (sum Hj m) (call 'signed/expr-sum-value-scale-right (f/lam [['sh nat]] (at Y 'sh j)) Cp m))]
                              [(mul one Cp) (mcong (column Y m j) one Cp Cp (at 'hcol j 'j-lt) (refl Cp))]
                              [Cp (one-times Cp)])
                     (le-trans (sum Fj m) (sum Gj m) (sum Hj m)
                               (a/sum-mono Fj Gj m 'jm (fn [i hi] (per-i i hi)))
                               (a/sum-mono Gj Hj m 'jn (fn [i hi] (lmono (at Y i j) (load Y p n i) Cp (y-lo Y i j hi 'j-lt) (at 'hload i hi)))))))))

(def average-bound-spec
  (let [Y 'Y p 'p m 'm n 'n Cp 'Cp
        P (f/lam [['ap nat]] (at p 'ap))
        byjob (f/lam [['aj nat]] (sum (f/lam [['ai nat]] (mul (at Y 'ai 'aj) (at p 'aj))) m))
        bymachine (f/lam [['am nat]] (sum (f/lam [['ak nat]] (mul (at Y 'am 'ak) (at p 'ak))) n))
        swapF (f/lam [['sj nat] ['si nat]] (mul (at Y 'si 'sj) (at p 'sj)))
        C (f/lam [['ac nat]] Cp)]
    (s/spec 'signed/pcmax-average-bound
            (into [['Y matrix] ['p family] ['Cp signed] ['m nat] ['n nat]] (competitor-binders Y p Cp m n))
            (le (sum P n) (mul Cp (of-nat/of-nat m)))
            (le-resp (sum bymachine m) (sum P n) (sum C m) (mul Cp (of-nat/of-nat m))
                     (a/chain (sum bymachine m)
                              [(sum byjob n) (sym (sum byjob n) (sum bymachine m) (call 'signed/expr-sum-value-swap swapF m n))]
                              [(sum P n) (a/sum-cong byjob P n 'aq (fn [j hj] (sym (at p j) (sum (f/lam [['ai nat]] (mul (at Y 'ai j) (at p j))) m) (spread Y p m j hj))))])
                     (call 'signed/expr-sum-constant-of-nat Cp m)
                     (a/sum-mono bymachine C m 'ab (fn [i hi] (at 'hload i hi)))))))

(def cancel-order-spec
  (s/spec 'signed/at-most-cancel-positive-right [['a signed] ['b signed] ['d signed] ['hd (lt s/zero 'd)] ['h (le (mul 'a 'd) (mul 'b 'd))]]
          (le 'a 'b)
          (cases (le 'a 'b) (le 'b 'a) (le 'a 'b) (call 'signed/at-most-total 'a 'b)
                 (f/lam [['ab (le 'a 'b)]] 'ab)
                 (f/lam [['ba (le 'b 'a)]]
                        (let [d0 (call 'signed/less-than-implies-at-most s/zero 'd 'hd)
                              same (call 'signed/at-most-antisymmetric (mul 'a 'd) (mul 'b 'd) 'h (rmono 'd 'b 'a d0 'ba))]
                          (a/eq-le 'a 'b (call 'signed/multiply-cancel-positive-right 'a 'b 'd 'hd same)))))))

(defn m [] (s/succ 'mm))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec indep/total-spec mmck/cancel-or-zero-spec mmck/cancel-positive-spec mmck/successor-positive-spec])

(def theorem-specs [job-bound-spec average-bound-spec cancel-order-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.sums.two-terms rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-pcmax-lower-bound borrowed-specs) (support/extend-with-shared :expr-sum-pcmax-lower-bound theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.pcmax-lower-bound))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
