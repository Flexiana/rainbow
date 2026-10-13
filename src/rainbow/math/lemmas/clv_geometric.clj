(ns rainbow.math.lemmas.clv-geometric
  "General lemmas: clv geometric. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def step-spec
  (let [[r R R1 D D1 E] '[cs-r cs-rr cs-r1 cs-d cs-d1 cs-e]]
    (s/spec 'signed/clv-step
            [['cs-r signed] ['cs-rr signed] ['cs-r1 signed] ['cs-d signed] ['cs-d1 signed] ['cs-e signed]
             ['cs-hr (eqv R1 (mul r R))] ['cs-hd (eqv (mul D1 E) D)]]
            (eqv (mul (mul R1 D1) E) (mul r (mul R D)))
            (a/chain (mul (mul R1 D1) E)
                     [(mul R1 (mul D1 E)) (call 'signed/multiply-associative R1 D1 E)]
                     [(mul (mul r R) D) (mcong R1 (mul r R) (mul D1 E) D 'cs-hr 'cs-hd)]
                     [(mul r (mul R D)) (call 'signed/multiply-associative r R D)]))))

(def telescope-spec
  (let [q 'gt-q E 'gt-e r 'gt-r qt #(at q %)
        lhs (fn [m] (sub (mul (sum q (s/succ m)) E) (mul r (sum q (s/succ m)))))
        rhs (fn [m] (sub (mul (qt s/nz) E) (mul r (qt m))))
        claim (fn [m] (f/forall [['gt-h (s/all-below m #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]] (eqv (lhs m) (rhs m))))]
    (s/spec 'signed/geometric-telescope [['gt-q family] ['gt-e signed] ['gt-r signed] ['gt-n nat]]
            (claim 'gt-n)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['gt-k nat]] (claim 'gt-k))
                   (f/lam [['gt-h (s/all-below s/nz #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]]
                          (let [S1 (add s/zero (qt s/nz))]   ; sum q 1 unfolds to 0 + q_0
                            (ring (sub (mul S1 E) (mul r S1)) (rhs s/nz))))
                   (f/lam [['gt-j nat] ['gt-ih (claim 'gt-j)] ['gt-h (s/all-below (s/succ 'gt-j) #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]]
                          (let [j 'gt-j j1 (s/succ j) S (sum q j1) qj (qt j) qj1 (qt j1)
                                weak (f/lam [['gt-i nat] ['gt-il (below 'gt-i j)]] (at 'gt-h 'gt-i (call 'nat/strict-below-weaken 'gt-i j 'gt-il)))
                                prev (at 'gt-ih weak)
                                step (at 'gt-h j (s/self-below j))]
                            ;; (S + q_{j+1}) E - r (S + q_{j+1}) ~ (S E - r S) + (q_{j+1} E - r q_{j+1})
                            ;;   ~ (q_0 E - r q_j) + (r q_j - r q_{j+1}) ~ q_0 E - r q_{j+1}
                            (a/chain (sub (mul (add S qj1) E) (mul r (add S qj1)))   ; sum q (j1 + 1) unfolds to S + q_{j1}
                                     [(add (sub (mul S E) (mul r S)) (sub (mul qj1 E) (mul r qj1))) (ring (sub (mul (add S qj1) E) (mul r (add S qj1))) (add (sub (mul S E) (mul r S)) (sub (mul qj1 E) (mul r qj1))))]
                                     [(add (rhs j) (sub (mul r qj) (mul r qj1)))
                                      (s/add-cong (sub (mul S E) (mul r S)) (rhs j) (sub (mul qj1 E) (mul r qj1)) (sub (mul r qj) (mul r qj1))
                                                  prev (s/add-cong (mul qj1 E) (mul r qj) (neg (mul r qj1)) (neg (mul r qj1)) step (refl (neg (mul r qj1)))))]
                                     [(rhs j1) (ring (add (rhs j) (sub (mul r qj) (mul r qj1))) (rhs j1))])))
                   'gt-n))))

(def scale-spec
  (let [[m S E r X] '[sc-m sc-s sc-e sc-r sc-x]]
    (s/spec 'signed/clv-scale [['sc-m signed] ['sc-s signed] ['sc-e signed] ['sc-r signed] ['sc-x signed] ['sc-h (eqv (sub (mul S E) (mul r S)) X)]]
            (eqv (mul (mul m S) (sub E r)) (mul m X))
            (a/chain (mul (mul m S) (sub E r))
                     [(mul m (sub (mul S E) (mul r S))) (ring (mul (mul m S) (sub E r)) (mul m (sub (mul S E) (mul r S))))]
                     [(mul m X) (mcong m m (sub (mul S E) (mul r S)) X (refl m) 'sc-h)]))))

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

(def theorem-specs [step-spec telescope-spec scale-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-clv-geometric theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.clv-geometric))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
