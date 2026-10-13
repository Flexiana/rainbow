(ns rainbow.math.lemmas.fulfil-readings
  "General lemmas: fulfil readings. The mathematical facts the corresponding checks rest on,
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
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

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
           [(add x (sub y x)) (s/add-cong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn msel "the checker's min(x, y): if-at-most x y x y" [x y] (sel y x (call 'signed/decide-at-most x y)))

(defn min-facts [x y v] (pconj (le v x) (pconj (le v y) (disj (eqv v x) (eqv v y)))))

(def min-select-spec
  (let [x 'ms-x y 'ms-y D (call 'signed/decide-at-most x y)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['ms-e (eqb b)]] (min-facts x y (sel y x b))))]
    (s/spec 'signed/min-select-cases [['ms-x signed] ['ms-y signed]]
            (min-facts x y (msel x y))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['ms-b bool]] (claim 'ms-b))
                          ;; decided false: y <= x, value y
                          (f/lam [['ms-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le y x) (pconj (le y y) (disj (eqv y x) (eqv y y)))
                                          (call 'signed/decide-at-most-false-reverse x y 'ms-e)
                                          (conjoin (le y y) (disj (eqv y x) (eqv y y)) (a/eq-le y y (refl y)) (inr (eqv y x) (eqv y y) (refl y)))))
                          ;; decided true: x <= y, value x
                          (f/lam [['ms-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le x x) (pconj (le x y) (disj (eqv x x) (eqv x y))) (a/eq-le x x (refl x))
                                          (conjoin (le x y) (disj (eqv x x) (eqv x y)) (call 'signed/decide-at-most-true-sound x y 'ms-e)
                                                   (inl (eqv x x) (eqv x y) (refl x)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn line-facts [o av sv d]
  (pconj (pconj (disj (eqv sv o) (eqv sv av)) (pconj (le sv o) (pconj (le sv av) (le s/zero sv))))
         (pconj (le s/zero d) (disj (eqv d s/zero) (eqv sv av)))))

(def line-spec
  (let [o 'pl-o av 'pl-a sv 'pl-s d 'pl-d v (msel o av)
        mf (call 'signed/min-select-cases o av)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        v-o (fst (le v o) (pconj (le v av) (disj (eqv v o) (eqv v av))) mf)
        v-a (fst (le v av) (disj (eqv v o) (eqv v av)) (snd (le v o) (pconj (le v av) (disj (eqv v o) (eqv v av))) mf))
        v-or (snd (le v av) (disj (eqv v o) (eqv v av)) (snd (le v o) (pconj (le v av) (disj (eqv v o) (eqv v av))) mf))
        ss (sym sv v 'pl-hs)
        s-o (le-resp v sv o o ss (refl o) v-o)
        s-a (le-resp v sv av av ss (refl av) v-a)
        s-or (cases (eqv v o) (eqv v av) (disj (eqv sv o) (eqv sv av)) v-or
                    (f/lam [['pl-vo (eqv v o)]] (inl (eqv sv o) (eqv sv av) (trans sv v o 'pl-hs 'pl-vo)))
                    (f/lam [['pl-va (eqv v av)]] (inr (eqv sv o) (eqv sv av) (trans sv v av 'pl-hs 'pl-va))))
        s-nn (cases (eqv sv o) (eqv sv av) (le s/zero sv) s-or
                    (f/lam [['pl-so (eqv sv o)]] (le-resp s/zero s/zero o sv (refl s/zero) (sym sv o 'pl-so) 'pl-ho))
                    (f/lam [['pl-sa (eqv sv av)]] (le-resp s/zero s/zero av sv (refl s/zero) (sym sv av 'pl-sa) 'pl-ha)))
        d-nn (le-resp s/zero s/zero (sub o sv) d (refl s/zero) (sym d (sub o sv) 'pl-hd) (diff-nn sv o s-o))
        d-or (cases (eqv sv o) (eqv sv av) (disj (eqv d s/zero) (eqv sv av)) s-or
                    (f/lam [['pl-so (eqv sv o)]]
                           (inl (eqv d s/zero) (eqv sv av)
                                (a/chain d [(sub o sv) 'pl-hd] [(sub o o) (s/add-cong o o (neg sv) (neg o) (refl o) (a/neg-cong sv o 'pl-so))]
                                         [s/zero (ring (sub o o) s/zero)])))
                    (f/lam [['pl-sa (eqv sv av)]] (inr (eqv d s/zero) (eqv sv av) 'pl-sa)))
        A (pconj (disj (eqv sv o) (eqv sv av)) (pconj (le sv o) (pconj (le sv av) (le s/zero sv))))
        B (pconj (le s/zero d) (disj (eqv d s/zero) (eqv sv av)))]
    (s/spec 'signed/pick-line [['pl-o signed] ['pl-a signed] ['pl-s signed] ['pl-d signed]
                               ['pl-ho (le s/zero o)] ['pl-ha (le s/zero av)] ['pl-hs (eqv sv v)] ['pl-hd (eqv d (sub o sv))]]
            (line-facts o av sv d)
            (conjoin A B
                     (conjoin (disj (eqv sv o) (eqv sv av)) (pconj (le sv o) (pconj (le sv av) (le s/zero sv))) s-or
                              (conjoin (le sv o) (pconj (le sv av) (le s/zero sv)) s-o (conjoin (le sv av) (le s/zero sv) s-a s-nn)))
                     (conjoin (le s/zero d) (disj (eqv d s/zero) (eqv sv av)) d-nn d-or)))))

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

(def theorem-specs [min-select-spec line-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-fulfil-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.fulfil-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
