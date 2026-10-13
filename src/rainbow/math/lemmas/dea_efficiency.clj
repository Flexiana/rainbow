(ns rainbow.math.lemmas.dea-efficiency
  "General lemmas: dea efficiency. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn assoc* [x y z] (call 'signed/multiply-associative x y z))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(def bilinear-swap-spec
  (let [a 'a b 'b M 'M p 'p q 'q
        inner-b (fn [r] (sum (f/lam [['ib nat]] (mul (at b 'ib) (at M r 'ib))) q))
        inner-a (fn [j] (sum (f/lam [['ia nat]] (mul (at a 'ia) (at M 'ia j))) p))
        L (f/lam [['l1 nat]] (mul (at a 'l1) (inner-b 'l1)))
        L2 (f/lam [['l2 nat]] (sum (f/lam [['l3 nat]] (mul (at a 'l2) (mul (at b 'l3) (at M 'l2 'l3)))) q))
        T (f/lam [['tr nat] ['tj nat]] (mul (at a 'tr) (mul (at b 'tj) (at M 'tr 'tj))))
        R2 (f/lam [['r2 nat]] (sum (f/lam [['r3 nat]] (mul (at a 'r3) (mul (at b 'r2) (at M 'r3 'r2)))) p))
        R3 (f/lam [['r4 nat]] (sum (f/lam [['r5 nat]] (mul (at b 'r4) (mul (at a 'r5) (at M 'r5 'r4)))) p))
        R (f/lam [['r1 nat]] (mul (at b 'r1) (inner-a 'r1)))
        flip (fn [x y z] (a/chain (mul x (mul y z)) [(mul (mul x y) z) (sym (mul (mul x y) z) (mul x (mul y z)) (assoc* x y z))]
                                  [(mul (mul y x) z) (mcong (mul x y) (mul y x) z z (comm x y) (refl z))]
                                  [(mul y (mul x z)) (assoc* y x z)]))]
    (s/spec 'signed/bilinear-swap [['a family] ['b family] ['M matrix] ['p nat] ['q nat]]
            (eqv (sum L p) (sum R q))
            (a/chain (sum L p)
                     [(sum L2 p) (a/sum-cong L L2 p 'ba (fn [r _] (call 'signed/expr-sum-value-scale-left (f/lam [['ib nat]] (mul (at b 'ib) (at M r 'ib))) (at a r) q)))]
                     [(sum R2 q) (call 'signed/expr-sum-value-swap T q p)]
                     [(sum R3 q) (a/sum-cong R2 R3 q 'bb
                                             (fn [j _] (a/sum-cong (f/lam [['r3 nat]] (mul (at a 'r3) (mul (at b j) (at M 'r3 j))))
                                                                   (f/lam [['r5 nat]] (mul (at b j) (mul (at a 'r5) (at M 'r5 j)))) p 'bc
                                                                   (fn [r _] (flip (at a r) (at b j) (at M r j))))))]
                     [(sum R q) (a/sum-cong R3 R q 'bd
                                            (fn [j _] (sym (mul (at b j) (inner-a j)) (sum (f/lam [['r5 nat]] (mul (at b j) (mul (at a 'r5) (at M 'r5 j)))) p)
                                                           (call 'signed/expr-sum-value-scale-left (f/lam [['ia nat]] (mul (at a 'ia) (at M 'ia j))) (at b j) p))))]))))

(defn wsum [w M k j] (sum (f/lam [['wk nat]] (mul (at w 'wk) (at M 'wk j))) k))

(defn lsum [lam M n i] (sum (f/lam [['lk nat]] (mul (at lam 'lk) (at M i 'lk))) n))

(defn multiplier-binders [X Y u v m s n]
  [['hu (s/all-below s #(le s/zero (at u %)))]
   ['hv (s/all-below m #(le s/zero (at v %)))]
   ['hnorm (eqv (wsum v X m s/nz) one)]
   ['hmult (s/all-below n #(le (wsum u Y s %) (wsum v X m %)))]])

(defn envelopment-binders [X Y lam th m s n]
  [['hlam (s/all-below n #(le s/zero (at lam %)))]
   ['hin (s/all-below m #(le (lsum lam X n %) (mul th (at X % s/nz))))]
   ['hout (s/all-below s #(le (at Y % s/nz) (lsum lam Y n %)))]])

(def weak-duality-spec
  (let [X 'X Y 'Y u 'u v 'v lam 'lam th 'th m 'm s 's n 'n
        U0 (wsum u Y s s/nz)
        A1 (f/lam [['a1 nat]] (mul (at u 'a1) (lsum lam Y n 'a1)))
        A2 (f/lam [['a2 nat]] (mul (at lam 'a2) (wsum u Y s 'a2)))
        A3 (f/lam [['a3 nat]] (mul (at lam 'a3) (wsum v X m 'a3)))
        A4 (f/lam [['a4 nat]] (mul (at v 'a4) (lsum lam X n 'a4)))
        A5 (f/lam [['a5 nat]] (mul (at v 'a5) (mul th (at X 'a5 s/nz))))
        A6 (f/lam [['a6 nat]] (mul th (mul (at v 'a6) (at X 'a6 s/nz))))
        XT (f/lam [['xj nat] ['xi nat]] (at X 'xi 'xj))
        step1 (a/sum-mono (f/lam [['wk nat]] (mul (at u 'wk) (at Y 'wk s/nz))) A1 s 'da
                          (fn [r hr] (lmono (at u r) (at Y r s/nz) (lsum lam Y n r) (at 'hu r hr) (at 'hout r hr))))
        eq2 (call 'signed/bilinear-swap u lam Y s n)
        step3 (a/sum-mono A2 A3 n 'db (fn [j hj] (lmono (at lam j) (wsum u Y s j) (wsum v X m j) (at 'hlam j hj) (at 'hmult j hj))))
        eq4 (call 'signed/bilinear-swap lam v XT n m)
        step5 (a/sum-mono A4 A5 m 'dc (fn [i hi] (lmono (at v i) (lsum lam X n i) (mul th (at X i s/nz)) (at 'hv i hi) (at 'hin i hi))))
        eq6 (a/chain (sum A5 m)
                     [(sum A6 m) (a/sum-cong A5 A6 m 'dd
                                             (fn [i _] (let [vi (at v i) xi (at X i s/nz)]
                                                         (a/chain (mul vi (mul th xi)) [(mul (mul vi th) xi) (sym (mul (mul vi th) xi) (mul vi (mul th xi)) (assoc* vi th xi))]
                                                                  [(mul (mul th vi) xi) (mcong (mul vi th) (mul th vi) xi xi (comm vi th) (refl xi))]
                                                                  [(mul th (mul vi xi)) (assoc* th vi xi)]))))]
                     [(mul th (wsum v X m s/nz)) (sym (mul th (wsum v X m s/nz)) (sum A6 m) (call 'signed/expr-sum-value-scale-left (f/lam [['wk nat]] (mul (at v 'wk) (at X 'wk s/nz))) th m))]
                     [(mul th one) (mcong th th (wsum v X m s/nz) one (refl th) 'hnorm)]
                     [th (a/chain (mul th one) [(mul one th) (comm th one)] [th (call 'signed/multiply-one-left th)])])]
    (s/spec 'signed/dea-weak-duality
            (-> [['X matrix] ['Y matrix] ['u family] ['v family] ['lam family] ['th signed] ['m nat] ['s nat] ['n nat]]
                (into (multiplier-binders X Y u v m s n)) (into (envelopment-binders X Y lam th m s n)))
            (le U0 th)
            (le-trans U0 (sum A1 s) th step1
                      (le-resp (sum A2 n) (sum A1 s) th th (sym (sum A1 s) (sum A2 n) eq2) (refl th)
                               (le-trans (sum A2 n) (sum A3 n) th step3
                                         (le-resp (sum A4 m) (sum A3 n) (sum A5 m) th (sym (sum A3 n) (sum A4 m) eq4) eq6 step5)))))))

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
  ({:conditions (symbol "signed" (str "dea-conditions-" stem)) :accepted (symbol "signed" (str "dea-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-dea-" stem))} kind))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(def theorem-specs [bilinear-swap-spec weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-dea-efficiency theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.dea-efficiency))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
