(ns rainbow.math.lemmas.mccormick-sandwich
  "General lemmas: mccormick sandwich. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.lemmas.stochastic-dominance :as sd]
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

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn diff-np [x y h] (le-resp (sub x y) (sub x y) (sub y y) s/zero (refl (sub x y)) (ring (sub y y) s/zero) (call 'signed/add-right-monotone x y (neg y) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn est [a b x y] (sub (add (mul a y) (mul x b)) (mul a b)))

(def under-spec
  (let [[a b x y] '[mu-a mu-b mu-x mu-y] E (est a b x y) P (mul (sub x a) (sub y b))]
    (s/spec 'signed/mccormick-under [['mu-a signed] ['mu-b signed] ['mu-x signed] ['mu-y signed] ['mu-h (le s/zero P)]]
            (le E (mul x y))
            (le-resp (add E s/zero) E (add E P) (mul x y) (ring (add E s/zero) E) (ring (add E P) (mul x y))
                     (call 'signed/add-left-monotone s/zero P E 'mu-h)))))

(def over-spec
  (let [[a b x y] '[mo-a mo-b mo-x mo-y] E (est a b x y) Q (mul (sub a x) (sub y b))]
    (s/spec 'signed/mccormick-over [['mo-a signed] ['mo-b signed] ['mo-x signed] ['mo-y signed] ['mo-h (le s/zero Q)]]
            (le (mul x y) E)
            (le-resp (add (mul x y) s/zero) (mul x y) (add (mul x y) Q) E (ring (add (mul x y) s/zero) (mul x y)) (ring (add (mul x y) Q) E)
                     (call 'signed/add-left-monotone s/zero Q (mul x y) 'mo-h)))))

(defn coord-prop [X Y XL XU YL YU L H]
  (let [u1 (est XL YL X Y) u2 (est XU YU X Y) o1 (est XU YL X Y) o2 (est XL YU X Y) XY (mul X Y)]
    (pconj (pconj (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)))
           (pconj (pconj (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)))
                  (pconj (le L XY) (le XY H))))))

(def coordinate-spec
  (let [[X Y XL XU YL YU L H] '[mt-x mt-y mt-xl mt-xu mt-yl mt-yu mt-lo mt-hi]
        u1 (est XL YL X Y) u2 (est XU YU X Y) o1 (est XU YL X Y) o2 (est XL YU X Y) XY (mul X Y)
        A1 (sub L u1) A2 (sub L u2) B1 (sub o1 H) B2 (sub o2 H)
        hyps [['mt-g0 (le XL X)] ['mt-g1 (le X XU)] ['mt-g2 (le YL Y)] ['mt-g3 (le Y YU)]
              ['mt-g4 (le u1 L)] ['mt-g5 (le u2 L)] ['mt-g6 (eqv (mul A1 A2) s/zero)]
              ['mt-g8 (le H o1)] ['mt-g9 (le H o2)] ['mt-g10 (eqv (mul B1 B2) s/zero)]]
        ldisj (cases (eqv A1 s/zero) (eqv A2 s/zero) (disj (eqv L u1) (eqv L u2)) (call 'signed/multiply-zero-split A1 A2 'mt-g6)
                     (f/lam [['mk-a (eqv A1 s/zero)]] (inl (eqv L u1) (eqv L u2) (sym u1 L (from-diff u1 L 'mk-a))))
                     (f/lam [['mk-b (eqv A2 s/zero)]] (inr (eqv L u1) (eqv L u2) (sym u2 L (from-diff u2 L 'mk-b)))))
        hdisj (cases (eqv B1 s/zero) (eqv B2 s/zero) (disj (eqv H o1) (eqv H o2)) (call 'signed/multiply-zero-split B1 B2 'mt-g10)
                     (f/lam [['ml-a (eqv B1 s/zero)]] (inl (eqv H o1) (eqv H o2) (from-diff H o1 'ml-a)))
                     (f/lam [['ml-b (eqv B2 s/zero)]] (inr (eqv H o1) (eqv H o2) (from-diff H o2 'ml-b))))
        u1-xy (call 'signed/mccormick-under XL YL X Y (nn-prod (sub X XL) (sub Y YL) (diff-nn XL X 'mt-g0) (diff-nn YL Y 'mt-g2)))
        u2-xy (call 'signed/mccormick-under XU YU X Y
                    (call 'signed/nonpositive-product-nonnegative (sub X XU) (sub Y YU) (diff-np X XU 'mt-g1) (diff-np Y YU 'mt-g3)))
        xy-o1 (call 'signed/mccormick-over XU YL X Y (nn-prod (sub XU X) (sub Y YL) (diff-nn X XU 'mt-g1) (diff-nn YL Y 'mt-g2)))
        xy-o2 (call 'signed/mccormick-over XL YU X Y
                    (call 'signed/nonpositive-product-nonnegative (sub XL X) (sub Y YU) (diff-np XL X 'mt-g0) (diff-np Y YU 'mt-g3)))
        lo-xy (cases (eqv L u1) (eqv L u2) (le L XY) ldisj
                     (f/lam [['mm-1 (eqv L u1)]] (le-resp u1 L XY XY (sym L u1 'mm-1) (refl XY) u1-xy))
                     (f/lam [['mm-2 (eqv L u2)]] (le-resp u2 L XY XY (sym L u2 'mm-2) (refl XY) u2-xy)))
        xy-hi (cases (eqv H o1) (eqv H o2) (le XY H) hdisj
                     (f/lam [['mn-1 (eqv H o1)]] (le-resp XY XY o1 H (refl XY) (sym H o1 'mn-1) xy-o1))
                     (f/lam [['mn-2 (eqv H o2)]] (le-resp XY XY o2 H (refl XY) (sym H o2 'mn-2) xy-o2)))
        LP (pconj (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)))
        HP (pconj (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)))
        SP (pconj (le L XY) (le XY H))]
    (s/spec 'signed/mccormick-coordinate
            (into [['mt-x signed] ['mt-y signed] ['mt-xl signed] ['mt-xu signed] ['mt-yl signed] ['mt-yu signed] ['mt-lo signed] ['mt-hi signed]] hyps)
            (coord-prop X Y XL XU YL YU L H)
            (conjoin LP (pconj HP SP)
                     (conjoin (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)) ldisj (conjoin (le u1 L) (le u2 L) 'mt-g4 'mt-g5))
                     (conjoin HP SP
                              (conjoin (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)) hdisj (conjoin (le H o1) (le H o2) 'mt-g8 'mt-g9))
                              (conjoin (le L XY) (le XY H) lo-xy xy-hi))))))

(defn coord-args [{:keys [x y xL xU yL yU lo hi]} i] (mapv #(at % i) [x y xL xU yL yU lo hi]))

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

(def theorem-specs [under-spec over-spec coordinate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-mccormick-sandwich [sd/nonpos-product-spec]) (support/extend-with-shared :expr-sum-mccormick-sandwich theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.mccormick-sandwich))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
