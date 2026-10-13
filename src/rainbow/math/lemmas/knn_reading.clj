(ns rainbow.math.lemmas.knn-reading
  "General lemmas: knn reading. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.abc-class :as abc]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(defn gap-le [x y h]
  (le-resp (add (sub x y) y) x (add s/zero y) y (ring (add (sub x y) y) x) (ring (add s/zero y) y)
           (call 'signed/add-right-monotone (sub x y) s/zero y h)))

(defn row [d z n i] (sum (f/lam [['kn-j nat]] (mul (sub one (at z 'kn-j)) (abc/strict-ind (at d 'kn-j) (at d i)))) n))

(def nearer-spec
  (let [d 'kn-d z 'kn-z n 'kn-n i 'kn-i j 'kn-j di (at d i) dj (at d j) zi (at z i) zj (at z j)
        R (row d z n i)
        T (f/lam [['kn-j nat]] (mul (sub one (at z 'kn-j)) (abc/strict-ind (at d 'kn-j) di)))
        r0 (a/chain R [(mul one R) (sym (mul one R) R (one-times R))]
                    [(mul zi R) (mcong one zi R R (sym zi one 'kn-zi) (refl R))]
                    [s/zero (at 'kn-top i 'kn-hi)])
        tnn (f/lam [['kt-j nat] ['kt-h (below 'kt-j n)]]
                   (nonneg-prod (sub one (at z 'kt-j)) (abc/strict-ind (at d 'kt-j) di)
                                (call 'signed/one-minus-nonnegative (at z 'kt-j) (call 'signed/zero-one-at-most-one (at z 'kt-j) (at 'kn-01 'kt-j 'kt-h)))
                                (call 'signed/strict-indicator-nonnegative (at d 'kt-j) di)))
        each (call 'signed/expr-sum-value-nonnegative-terms-zero T n tnn r0)
        I (abc/strict-ind dj di)
        I0 (a/chain I [(mul one I) (sym (mul one I) I (one-times I))]
                    [(mul (sub one s/zero) I) (mcong one (sub one s/zero) I I (ring one (sub one s/zero)) (refl I))]
                    [(mul (sub one zj) I) (mcong (sub one s/zero) (sub one zj) I I
                                                 (s/add-cong one one (neg s/zero) (neg zj) (refl one) (a/neg-cong s/zero zj (sym zj s/zero 'kn-zj)))
                                                 (refl I))]
                    [s/zero (at each j 'kn-hj)])]
    (s/spec 'signed/knn-selected-nearer
            [['kn-d family] ['kn-z family] ['kn-n nat]
             ['kn-01 (s/all-below n #(zero-one (at z %)))]
             ['kn-top (s/all-below n #(eqv (mul (at z %) (row d z n %)) s/zero))]
             ['kn-i nat] ['kn-hi (below i n)] ['kn-j nat] ['kn-hj (below j n)]
             ['kn-zi (eqv zi one)] ['kn-zj (eqv zj s/zero)]]
            (le di dj)
            (call 'signed/strict-indicator-zero-order dj di I0))))

(defn majority-prop [y k tC] (pconj (f/arrow (eqv y one) (le k tC)) (f/arrow (eqv y s/zero) (le tC k))))

(def majority-spec
  (let [y 'mj-y k 'mj-k tC 'mj-c]
    (s/spec 'signed/knn-majority
            [['mj-y signed] ['mj-k signed] ['mj-c signed]
             ['mj-1 (le (mul y (add k (neg tC))) s/zero)]
             ['mj-0 (le (mul (add one (neg y)) (add tC (neg k))) s/zero)]]
            (majority-prop y k tC)
            (conjoin (f/arrow (eqv y one) (le k tC)) (f/arrow (eqv y s/zero) (le tC k))
                     (f/lam [['mj-y1 (eqv y one)]]
                            (gap-le k tC (le-resp (mul y (sub k tC)) (sub k tC) s/zero s/zero
                                                  (a/chain (mul y (sub k tC)) [(mul one (sub k tC)) (mcong y one (sub k tC) (sub k tC) 'mj-y1 (refl (sub k tC)))]
                                                           [(sub k tC) (one-times (sub k tC))])
                                                  (refl s/zero) 'mj-1)))
                     (f/lam [['mj-y0 (eqv y s/zero)]]
                            (gap-le tC k (le-resp (mul (sub one y) (sub tC k)) (sub tC k) s/zero s/zero
                                                  (a/chain (mul (sub one y) (sub tC k))
                                                           [(mul (sub one s/zero) (sub tC k)) (mcong (sub one y) (sub one s/zero) (sub tC k) (sub tC k)
                                                                                                     (s/add-cong one one (neg y) (neg s/zero) (refl one) (a/neg-cong y s/zero 'mj-y0))
                                                                                                     (refl (sub tC k)))]
                                                           [(mul one (sub tC k)) (mcong (sub one s/zero) one (sub tC k) (sub tC k) (ring (sub one s/zero) one) (refl (sub tC k)))]
                                                           [(sub tC k) (one-times (sub tC k))])
                                                  (refl s/zero) 'mj-0)))))))

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

(def theorem-specs [nearer-spec majority-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.lemmas.abc-class rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.distributive rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-knn-reading theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.knn-reading))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
