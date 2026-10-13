(ns rainbow.math.lemmas.ncd-readings
  "General lemmas: ncd readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.fulfil-readings :as ful]
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

(defn stepsel "the checker's (c <= 0 ? min(M, x + 1) : 0)" [c x M] (sel s/zero (ful/msel M (add x one)) (call 'signed/decide-at-most c s/zero)))

(defn minf [M x1 v] (pconj (le v M) (pconj (le v x1) (disj (eqv v M) (eqv v x1)))))

(defn step-facts [c x M v]
  (let [x1 (add x one)]
    (pconj (disj (pconj (le c s/zero) (minf M x1 v)) (eqv v s/zero))
           (f/forall [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]] (pconj (le s/zero v) (le v M))))))

(def step-spec
  (let [c 'ns-c x 'ns-x M 'ns-M v 'ns-v x1 (add x one) w (ful/msel M x1) D (call 'signed/decide-at-most c s/zero)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['ns-de (eqb b)] ['ns-hv (eqv v (sel s/zero w b))]] (step-facts c x M v)))
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        L (pconj (le c s/zero) (minf M x1 v)) R (eqv v s/zero)
        Rng (f/forall [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]] (pconj (le s/zero v) (le v M)))]
    (s/spec 'signed/ncd-step [['ns-c signed] ['ns-x signed] ['ns-M signed] ['ns-v signed] ['ns-hv (eqv v (stepsel c x M))]]
            (step-facts c x M v)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['ns-b bool]] (claim 'ns-b))
                          ;; a claim: v ~ 0
                          (f/lam [['ns-de (eqb (f/const* 'data/false []))] ['ns-hv (eqv v s/zero)]]
                                 (conjoin (disj L R) Rng (inr L R 'ns-hv)
                                          (f/lam [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]]
                                                 (conjoin (le s/zero v) (le v M) (a/eq-le s/zero v (sym v s/zero 'ns-hv))
                                                          (le-resp s/zero v M M (sym v s/zero 'ns-hv) (refl M) 'ns-M0)))))
                          ;; clean: v ~ min(M, x + 1)
                          (f/lam [['ns-de (eqb (f/const* 'data/true []))] ['ns-hv (eqv v w)]]
                                 (let [mf (call 'signed/min-select-cases M x1)
                                       w-M (fst (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf)
                                       w-x (fst (le w x1) (disj (eqv w M) (eqv w x1)) (snd (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf))
                                       w-or (snd (le w x1) (disj (eqv w M) (eqv w x1)) (snd (le w M) (pconj (le w x1) (disj (eqv w M) (eqv w x1))) mf))
                                       sv (sym v w 'ns-hv)
                                       v-M (le-resp w v M M sv (refl M) w-M)
                                       v-x (le-resp w v x1 x1 sv (refl x1) w-x)
                                       v-or (cases (eqv w M) (eqv w x1) (disj (eqv v M) (eqv v x1)) w-or
                                                   (f/lam [['ns-wm (eqv w M)]] (inl (eqv v M) (eqv v x1) (trans v w M 'ns-hv 'ns-wm)))
                                                   (f/lam [['ns-wx (eqv w x1)]] (inr (eqv v M) (eqv v x1) (trans v w x1 'ns-hv 'ns-wx))))]
                                   (conjoin (disj L R) Rng
                                            (inl L R (conjoin (le c s/zero) (minf M x1 v) (call 'signed/decide-at-most-true-sound c s/zero 'ns-de)
                                                              (conjoin (le v M) (pconj (le v x1) (disj (eqv v M) (eqv v x1))) v-M
                                                                       (conjoin (le v x1) (disj (eqv v M) (eqv v x1)) v-x v-or))))
                                            (f/lam [['ns-x0 (le s/zero x)] ['ns-xM (le x M)] ['ns-M0 (le s/zero M)]]
                                                   (let [x1-nn (le-trans s/zero x x1 'ns-x0
                                                                         (le-resp (add x s/zero) x (add x one) x1 (ring (add x s/zero) x) (refl x1)
                                                                                  (le-resp (add s/zero x) (add x s/zero) (add one x) (add x one) (ring (add s/zero x) (add x s/zero)) (ring (add one x) (add x one))
                                                                                           (call 'signed/add-right-monotone s/zero one x (f/const* 'signed/zero-at-most-one [])))))]
                                                     (conjoin (le s/zero v) (le v M)
                                                              (cases (eqv v M) (eqv v x1) (le s/zero v) v-or
                                                                     (f/lam [['ns-vm (eqv v M)]] (le-resp s/zero s/zero M v (refl s/zero) (sym v M 'ns-vm) 'ns-M0))
                                                                     (f/lam [['ns-vx (eqv v x1)]] (le-resp s/zero s/zero x1 v (refl s/zero) (sym v x1 'ns-vx) x1-nn)))
                                                              v-M))))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'ns-hv))))

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

(def theorem-specs [step-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-ncd-readings [ful/min-select-spec]) (support/extend-with-shared :expr-sum-ncd-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.ncd-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
