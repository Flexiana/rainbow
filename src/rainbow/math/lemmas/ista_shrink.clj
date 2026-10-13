(ns rainbow.math.lemmas.ista-shrink
  "General lemmas: ista shrink. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.square-zero :as square-zero]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn drop-nn [x y h] (le-resp (add x (neg y)) (sub x y) (add x (neg s/zero)) x (refl (sub x y)) (ring (add x (neg s/zero)) x)
                                (call 'signed/add-left-monotone (neg y) (neg s/zero) x (call 'signed/negate-reverses-order s/zero y h))))

(defn diff-np [x y h] (le-resp (sub x y) (sub x y) (sub y y) s/zero (refl (sub x y)) (ring (sub y y) s/zero) (call 'signed/add-right-monotone x y (neg y) h)))

(defn reading-prop [A Y M X C]
  (let [G (sub A C)]
    (pconj (pconj (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)))
           (pconj (le M A)
                  (pconj (le (mul X X) (mul Y Y))
                         (f/forall [['st-z (le A C)]] (eqv X s/zero)))))))

(def reading-spec
  (let [[A Y M X C] '[st-a st-y st-m st-x st-c]
        G (sub A C) B (sub M G)
        mx (cases (eqv M s/zero) (eqv B s/zero) (disj (eqv M s/zero) (eqv M G)) (call 'signed/multiply-zero-split M B 'st-hp)
                  (f/lam [['st-0 (eqv M s/zero)]] (inl (eqv M s/zero) (eqv M G) 'st-0))
                  (f/lam [['st-1 (eqv B s/zero)]] (inr (eqv M s/zero) (eqv M G) (sym G M (from-diff G M 'st-1)))))
        m-le-a (cases (eqv M s/zero) (eqv M G) (le M A) mx
                      (f/lam [['st-2 (eqv M s/zero)]] (le-resp s/zero M A A (sym M s/zero 'st-2) (refl A) 'st-ha))
                      (f/lam [['st-3 (eqv M G)]] (le-resp G M A A (sym M G 'st-3) (refl A) (drop-nn A C 'st-hc))))
        ;; m m <= a a, so x x ~ m m <= a a ~ y y
        mm-aa (le-trans (mul M M) (mul M A) (mul A A) (lmono M M A 'st-hm m-le-a) (rmono A M A 'st-ha m-le-a))
        shrink (le-resp (mul M M) (mul X X) (mul A A) (mul Y Y) (sym (mul X X) (mul M M) 'st-hx) 'st-hy mm-aa)
        dead (f/lam [['st-z (le A C)]]
                    (let [g-np (diff-np A C 'st-z)
                          m0 (cases (eqv M s/zero) (eqv M G) (eqv M s/zero) mx
                                    (f/lam [['st-4 (eqv M s/zero)]] 'st-4)
                                    (f/lam [['st-5 (eqv M G)]]
                                           (anti M s/zero (le-resp G M s/zero s/zero (sym M G 'st-5) (refl s/zero) g-np) 'st-hm)))
                          xx0 (a/chain (mul X X) [(mul M M) 'st-hx]
                                       [(mul s/zero s/zero) (a/mul-cong M s/zero M s/zero m0 m0)]
                                       [s/zero (ring (mul s/zero s/zero) s/zero)])]
                      (call 'signed/square-zero-reflects X xx0)))]
    (s/spec 'signed/soft-threshold-reading
            [['st-a signed] ['st-y signed] ['st-m signed] ['st-x signed] ['st-c signed]
             ['st-ha (le s/zero A)] ['st-hy (eqv (mul A A) (mul Y Y))] ['st-hg (le G M)] ['st-hm (le s/zero M)]
             ['st-hp (eqv (mul M B) s/zero)] ['st-hx (eqv (mul X X) (mul M M))] ['st-hc (le s/zero C)]]
            (reading-prop A Y M X C)
            (conjoin (pconj (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)))
                     (pconj (le M A) (pconj (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero))))
                     (conjoin (disj (eqv M s/zero) (eqv M G)) (pconj (le s/zero M) (le G M)) mx (conjoin (le s/zero M) (le G M) 'st-hm 'st-hg))
                     (conjoin (le M A) (pconj (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero))) m-le-a
                              (conjoin (le (mul X X) (mul Y Y)) (f/forall [['st-z (le A C)]] (eqv X s/zero)) shrink dead))))))

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

(def theorem-specs [reading-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.nnrat.quadratic-zero rainbow.math.rational.signed.square-zero])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-ista-shrink theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.ista-shrink))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
