(ns rainbow.math.lemmas.kmeans-nearest
  "General lemmas: kmeans nearest. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.ufl-gap :as ufl]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn positive-part [t] (ufl/positive-part t))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def zero-one-nonneg-spec
  (let [goal (le s/zero 'x)]
    (s/spec 'signed/zero-one-nonnegative [['x signed] ['h (eqv (mul 'x (sub one 'x)) s/zero)]]
            goal
            (call 'proposition/use-disjunction (eqv 'x s/zero) (eqv (sub one 'x) s/zero) goal
                  (call 'signed/multiply-zero-split 'x (sub one 'x) 'h)
                  (f/lam [['hx (eqv 'x s/zero)]] (a/eq-le s/zero 'x (sym 'x s/zero 'hx)))
                  (f/lam [['h1 (eqv (sub one 'x) s/zero)]]
                         ;; x ~ 1 - (1 - x) ~ 1 - 0 ~ 1 >= 0
                         (le-resp s/zero s/zero one 'x (refl s/zero)
                                  (a/chain one [(sub one s/zero) (ring one (sub one s/zero))]
                                           [(sub one (sub one 'x)) (s/add-cong one one (neg s/zero) (neg (sub one 'x)) (refl one)
                                                                               (a/neg-cong s/zero (sub one 'x) (sym (sub one 'x) s/zero 'h1)))]
                                           ['x (ring (sub one (sub one 'x)) 'x)])
                                  (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one []))))))))

(defn worse [X d K j] (sum (f/lam [['wk nat]] (mul (at X 'wk) (positive-part (sub (at d 'wk) (at d j))))) K))

(defn nearest-sum [X d K] (sum (f/lam [['nj nat]] (worse X d K 'nj)) K))

(def nearest-spec
  (let [K 'K
        term (fn [k j] (mul (at 'X k) (positive-part (sub (at 'd k) (at 'd j)))))
        term-nonneg (fn [k j hk] (nonneg-prod (at 'X k) (positive-part (sub (at 'd k) (at 'd j))) (at 'x0 k hk)
                                              (call 'signed/positive-part-nonneg (sub (at 'd k) (at 'd j)))))
        worse-nonneg (fn [j] (call 'signed/expr-sum-value-nonnegative (f/lam [['wk nat]] (term 'wk j)) K
                                   (f/lam [['tk nat] ['tb (below 'tk K)]] (term-nonneg 'tk j 'tb))))
        W (f/lam [['nj nat]] (worse 'X 'd K 'nj))
        total-zero (call 'signed/at-most-antisymmetric (nearest-sum 'X 'd K) s/zero 'hnear
                         (call 'signed/expr-sum-value-nonnegative W K (f/lam [['oj nat] ['ob (below 'oj K)]] (worse-nonneg 'oj))))
        worse-zero (call 'signed/expr-sum-value-nonnegative-terms-zero W K
                         (f/lam [['oj nat] ['ob (below 'oj K)]] (worse-nonneg 'oj)) total-zero)
        term-zero (call 'signed/expr-sum-value-nonnegative-terms-zero (f/lam [['wk nat]] (term 'wk 'j)) K
                        (f/lam [['tk nat] ['tb (below 'tk K)]] (term-nonneg 'tk 'j 'tb))
                        (at worse-zero 'j 'hj))
        t (sub (at 'd 'k) (at 'd 'j)) pt (positive-part t)
        pos-zero (a/chain pt
                          [(mul one pt) (sym (mul one pt) pt (call 'signed/multiply-one-left pt))]
                          [(mul (at 'X 'k) pt) (a/mul-cong one (at 'X 'k) pt pt (sym (at 'X 'k) one 'hx) (refl pt))]
                          [s/zero (at term-zero 'k 'hk)])
        t-np (le-trans t pt s/zero (call 'signed/positive-part-upper t) (a/eq-le pt s/zero pos-zero))]
    (s/spec 'signed/kmeans-assigned-is-nearest
            [['X family] ['d family] ['K nat]
             ['x0 (s/all-below K #(le s/zero (at 'X %)))] ['hnear (le (nearest-sum 'X 'd K) s/zero)]
             ['k nat] ['hk (below 'k K)] ['hx (eqv (at 'X 'k) one)] ['j nat] ['hj (below 'j K)]]
            (le (at 'd 'k) (at 'd 'j))
            (call 'signed/add-of-at-most-subtract-local (at 'd 'j) (at 'd 'k) t-np))))

(def rearrange-spec
  (s/spec 'signed/add-of-at-most-subtract-local [['dj signed] ['dk signed] ['h (le (sub 'dk 'dj) s/zero)]]
          (le 'dk 'dj)
          (le-resp (add (sub 'dk 'dj) 'dj) 'dk (add s/zero 'dj) 'dj
                   (ring (add (sub 'dk 'dj) 'dj) 'dk) (ring (add s/zero 'dj) 'dj)
                   (call 'signed/add-right-monotone (sub 'dk 'dj) s/zero 'dj 'h))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [zero-one-nonneg-spec rearrange-spec nearest-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.lemmas.ufl-gap rainbow.math.lemmas.lp-duality rainbow.math.lemmas.bb-leaf-bound])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-kmeans-nearest theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.kmeans-nearest))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
