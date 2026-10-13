(ns rainbow.math.lemmas.auction-assignment
  "General lemmas: auction assignment. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.lemmas.bottleneck-assignment :as bap :refer [permutation-binders row-sum col-sum]]
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

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn net-row [z a p n i] (sum (f/lam [['nk nat]] (mul (at z i 'nk) (sub (at a i 'nk) (at p 'nk)))) n))

(defn value [z a n] (sum (f/lam [['vi nat]] (sum (f/lam [['vk nat]] (mul (at z 'vi 'vk) (at a 'vi 'vk))) n)) n))

(defn psum [p n] (sum (f/lam [['ps nat]] (at p 'ps)) n))

(def net-sum-spec
  (let [z 'z a 'a p 'p n 'n
        ZA (fn [i] (f/lam [['za nat]] (mul (at z i 'za) (at a i 'za))))
        ZP (fn [i] (f/lam [['zp nat]] (mul (at z i 'zp) (at p 'zp))))
        T (f/lam [['ti nat] ['tk nat]] (mul (at z 'ti 'tk) (at p 'tk)))
        per-row (fn [i] (a/chain (net-row z a p n i)
                                 [(sum (f/lam [['nd nat]] (sub (at (ZA i) 'nd) (at (ZP i) 'nd))) n)
                                  (a/sum-cong (f/lam [['nk nat]] (mul (at z i 'nk) (sub (at a i 'nk) (at p 'nk)))) (f/lam [['nd nat]] (sub (at (ZA i) 'nd) (at (ZP i) 'nd))) n 'na
                                              (fn [k _] (call 'signed/multiply-subtract-expand (at z i k) (at a i k) (at p k))))]
                                 [(sub (sum (ZA i) n) (sum (ZP i) n)) (call 'signed/expr-sum-value-subtract (ZA i) (ZP i) n)]))
        rows (f/lam [['ri nat]] (net-row z a p n 'ri))
        VA (f/lam [['vi nat]] (sum (ZA 'vi) n))
        VP (f/lam [['wi nat]] (sum (ZP 'wi) n))
        prices (a/chain (sum VP n)
                        [(sum (f/lam [['pk nat]] (sum (f/lam [['pi nat]] (mul (at z 'pi 'pk) (at p 'pk))) n)) n) (call 'signed/expr-sum-value-swap T n n)]
                        [(sum (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) n)
                         (a/sum-cong (f/lam [['pk nat]] (sum (f/lam [['pi nat]] (mul (at z 'pi 'pk) (at p 'pk))) n)) (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) n 'nb
                                     (fn [k _] (sym (mul (col-sum z n k) (at p k)) (sum (f/lam [['pi nat]] (mul (at z 'pi k) (at p k))) n)
                                                    (call 'signed/expr-sum-value-scale-right (f/lam [['ci nat]] (at z 'ci k)) (at p k) n))))]
                        [(psum p n) (a/sum-cong (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) (f/lam [['ps nat]] (at p 'ps)) n 'nc
                                                (fn [k hk] (trans (mul (col-sum z n k) (at p k)) (mul one (at p k)) (at p k)
                                                                  (mcong (col-sum z n k) one (at p k) (at p k) (at 'hcol k hk) (refl (at p k))) (one-times (at p k)))))])]
    (s/spec 'signed/assignment-net-sum
            [['z matrix] ['a matrix] ['p family] ['n nat] ['hcol (s/all-below n #(eqv (col-sum z n %) one))]]
            (eqv (sum rows n) (sub (value z a n) (psum p n)))
            (a/chain (sum rows n)
                     [(sum (f/lam [['rd nat]] (sub (at VA 'rd) (at VP 'rd))) n) (a/sum-cong rows (f/lam [['rd nat]] (sub (at VA 'rd) (at VP 'rd))) n 'nrow (fn [i _] (per-row i)))]
                     [(sub (sum VA n) (sum VP n)) (call 'signed/expr-sum-value-subtract VA VP n)]
                     [(sub (value z a n) (psum p n)) (s/add-cong (sum VA n) (value z a n) (neg (sum VP n)) (neg (psum p n)) (refl (sum VA n)) (a/neg-cong (sum VP n) (psum p n) prices))]))))

(def near-optimal-spec
  (let [a 'a x 'x y 'y p 'p eps 'eps n 'n
        G (fn [i] (net-row x a p n i))
        bound (fn [i] (add (G i) eps))
        ;; row i of y: sum_k y_ik (a_ik - p_k) <= G_i + eps
        row-le (fn [i hi]
                 (let [Yl (f/lam [['yl nat]] (mul (at y i 'yl) (sub (at a i 'yl) (at p 'yl))))
                       Yr (f/lam [['yr nat]] (mul (at y i 'yr) (bound i)))]
                   (le-resp (sum Yl n) (net-row y a p n i) (sum Yr n) (bound i) (refl (sum Yl n))
                            (a/chain (sum Yr n) [(mul (row-sum y n i) (bound i)) (sym (mul (row-sum y n i) (bound i)) (sum Yr n) (call 'signed/expr-sum-value-scale-right (f/lam [['rj nat]] (at y i 'rj)) (bound i) n))]
                                     [(mul one (bound i)) (mcong (row-sum y n i) one (bound i) (bound i) (at 'hrow i hi) (refl (bound i)))]
                                     [(bound i) (one-times (bound i))])
                            (a/sum-mono Yl Yr n 'ra
                                        (fn [k hk] (lmono (at y i k) (sub (at a i k) (at p k)) (bound i)
                                                          (call 'signed/zero-one-nonnegative (at y i k) (at 'hy01 i hi k hk)) (at 'hcs i hi k hk)))))))
        Yrows (f/lam [['yo nat]] (net-row y a p n 'yo))
        Bounds (f/lam [['bo nat]] (bound 'bo))
        Gs (f/lam [['go nat]] (G 'go))
        E (f/lam [['eo nat]] eps)
        total-le (a/sum-mono Yrows Bounds n 'rb (fn [i hi] (row-le i hi)))
        VY (value y a n) VX (value x a n) P (psum p n) nE (mul eps (of-nat/of-nat n))
        bounds-eq (a/chain (sum Bounds n)
                           [(add (sum Gs n) (sum E n)) (call 'signed/expr-sum-value-add Gs E n)]
                           [(add (sub VX P) nE) (s/add-cong (sum Gs n) (sub VX P) (sum E n) nE
                                                            (call 'signed/assignment-net-sum x a p n 'hxcol) (call 'signed/expr-sum-constant-of-nat eps n))])
        core (le-resp (sum Yrows n) (sub VY P) (sum Bounds n) (add (sub VX P) nE)
                      (call 'signed/assignment-net-sum y a p n 'hcol) bounds-eq total-le)]
    (s/spec 'signed/auction-near-optimal
            (-> [['a matrix] ['x matrix] ['p family] ['eps signed] ['n nat]
                 ['hxcol (s/all-below n #(eqv (col-sum x n %) one))]
                 ['hcs (f/forall [['ci nat] ['ci-lt (below 'ci n)] ['ck nat] ['ck-lt (below 'ck n)]] (le (sub (at a 'ci 'ck) (at p 'ck)) (add (G 'ci) eps)))]
                 ['y matrix]]
                (into (permutation-binders y n)))
            (le VY (add VX nE))
            (le-resp (add (sub VY P) P) VY (add (add (sub VX P) nE) P) (add VX nE)
                     (ring (add (sub VY P) P) VY) (ring (add (add (sub VX P) nE) P) (add VX nE))
                     (call 'signed/add-right-monotone (sub VY P) (add (sub VX P) nE) P core)))))

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

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec indep/subtract-expand-spec])

(def theorem-specs [net-sum-spec near-optimal-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-auction-assignment borrowed-specs) (support/extend-with-shared :expr-sum-auction-assignment theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.auction-assignment))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
