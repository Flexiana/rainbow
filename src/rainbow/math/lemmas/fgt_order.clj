(ns rainbow.math.lemmas.fgt-order
  "General lemmas: fgt order. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.deviation-rows :as deviation]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(defn lt [x y] (call 'signed/less-than x y))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-refl [x] (call 'signed/at-most-reflexive x))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn bool-cases [motive D false-case true-case]
  (f/app (f/app (f/const* 'data/Bool.rec [prop-level]) motive false-case true-case D)
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(defn clamp [v] (sel s/zero v (call 'signed/decide-at-most s/zero v)))

(defn clamp-facts [v w]
  (pconj (le s/zero (clamp v))
         (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le (clamp v) w)))
                (f/arrow (le v s/zero) (eqv (clamp v) s/zero)))))

(def clamp-spec
  (let [v 'fc-v w 'fc-w D (call 'signed/decide-at-most s/zero v)
        eqb (fn [b] (f/equality type-level bool D b))
        facts (fn [c] (pconj (le s/zero c) (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)))))
        build (fn [c nn bound zero]
                (conjoin (le s/zero c) (pconj (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)))
                         nn (conjoin (f/arrow (le v w) (f/arrow (le s/zero w) (le c w))) (f/arrow (le v s/zero) (eqv c s/zero)) bound zero)))]
    (s/spec 'signed/fgt-clamp-bounds [['fc-v signed] ['fc-w signed]]
            (clamp-facts v w)
            (bool-cases (f/lam [['fc-b bool]] (f/forall [['fc-e (eqb 'fc-b)]] (facts (sel s/zero v 'fc-b)))) D
                        ;; decided false: g = 0
                        (f/lam [['fc-e (eqb bfalse)]]
                               (build s/zero (le-refl s/zero)
                                      (f/lam [['fc-a (le v w)] ['fc-z (le s/zero w)]] 'fc-z)
                                      (f/lam [['fc-n (le v s/zero)]] (refl s/zero))))
                        ;; decided true: 0 <= v, g = v
                        (f/lam [['fc-e (eqb btrue)]]
                               (let [pos (call 'signed/decide-at-most-true-sound s/zero v 'fc-e)]
                                 (build v pos
                                        (f/lam [['fc-a (le v w)] ['fc-z (le s/zero w)]] 'fc-a)
                                        (f/lam [['fc-n (le v s/zero)]] (anti v s/zero 'fc-n pos)))))))))

(defn indicator [y z] (sel one s/zero (call 'signed/decide-at-most z y)))

(def gap-indicator-spec
  (let [[g y z] '[gi-g gi-y gi-z] D (call 'signed/decide-at-most z y) v (sub z y)
        eqb (fn [b] (f/equality type-level bool D b))
        goal (fn [b] (le g (mul z (sel one s/zero b))))
        cf (call 'signed/fgt-clamp-bounds v z)
        cnn (pleft (le s/zero (clamp v)) (pconj (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero))) cf)
        rest (pright (le s/zero (clamp v)) (pconj (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero))) cf)
        cbound (pleft (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero)) rest)
        czero (pright (f/arrow (le v z) (f/arrow (le s/zero z) (le (clamp v) z))) (f/arrow (le v s/zero) (eqv (clamp v) s/zero)) rest)
        ;; z - y <= z - 0 ~ z  (0 <= y)
        v-le-z (le-resp v v (sub z s/zero) z (refl v) (ring (sub z s/zero) z)
                        (call 'signed/add-left-monotone (neg y) (neg s/zero) z (call 'signed/negate-reverses-order s/zero y 'gi-hy)))]
    (s/spec 'signed/fgt-gap-indicator
            [['gi-g signed] ['gi-y signed] ['gi-z signed] ['gi-hg (eqv g (clamp v))] ['gi-hy (le s/zero y)] ['gi-hz (le s/zero z)]]
            (goal D)
            (bool-cases (f/lam [['gi-b bool]] (f/forall [['gi-e (eqb 'gi-b)]] (goal 'gi-b))) D
                        ;; decided false (not z <= y): indicator 1, g <= z ~ z 1
                        (f/lam [['gi-e (eqb bfalse)]]
                               (le-resp g g z (mul z one) (refl g) (sym (mul z one) z (trans (mul z one) (mul one z) z (call 'signed/multiply-commutative z one) (call 'signed/multiply-one-left z)))
                                        (le-resp (clamp v) g z z (sym g (clamp v) 'gi-hg) (refl z) (f/app (f/app cbound v-le-z) 'gi-hz))))
                        ;; decided true (z <= y): z - y <= 0, g ~ clamp ~ 0 ~ z 0
                        (f/lam [['gi-e (eqb btrue)]]
                               (let [zy (call 'signed/decide-at-most-true-sound z y 'gi-e)
                                     v-nonpos (le-resp v v (sub y y) s/zero (refl v) (ring (sub y y) s/zero)
                                                       (call 'signed/add-right-monotone z y (neg y) zy))
                                     g0 (trans g (clamp v) s/zero 'gi-hg (f/app czero v-nonpos))]
                                 (a/eq-le g (mul z s/zero) (trans g s/zero (mul z s/zero) g0 (sym (mul z s/zero) s/zero (call 'signed/multiply-zero-right z))))))))))

(defn fam [g] (f/lam [['ff-t nat]] (g 'ff-t)))

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

(def theorem-specs [clamp-spec gap-indicator-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-fgt-order [hhi/positive-spec]) (support/extend-with-shared :expr-sum-fgt-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.fgt-order))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
