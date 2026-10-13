(ns rainbow.math.lemmas.state-price
  "General lemmas: state price. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn lt [x y] (call 'signed/less-than x y))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn payoff [D theta J s] (sum (f/lam [['pj nat]] (mul (at D s 'pj) (at theta 'pj))) J))

(defn cost [pi theta J] (sum (f/lam [['cj nat]] (mul (at pi 'cj) (at theta 'cj))) J))

(defn state-value [q D theta S J] (sum (f/lam [['vs nat]] (mul (at q 'vs) (payoff D theta J 'vs))) S))

(defn priced [q D S j] (sum (f/lam [['ps nat]] (mul (at q 'ps) (at D 'ps j))) S))

(defn pricing-binder [D pi q S J] ['hpi (s/all-below J #(eqv (priced q D S %) (at pi %)))])

(def pricing-spec
  (let [D 'D pi 'pi q 'q theta 'theta S 'S J 'J
        A (f/lam [['a1 nat]] (mul (priced q D S 'a1) (at theta 'a1)))
        B (f/lam [['b1 nat]] (sum (f/lam [['b2 nat]] (mul (mul (at q 'b2) (at D 'b2 'b1)) (at theta 'b1))) S))
        T (f/lam [['tj nat] ['ts nat]] (mul (mul (at q 'ts) (at D 'ts 'tj)) (at theta 'tj)))
        C (f/lam [['c1 nat]] (sum (f/lam [['c2 nat]] (mul (mul (at q 'c1) (at D 'c1 'c2)) (at theta 'c2))) J))]
    (s/spec 'signed/state-price-pricing
            [['D matrix] ['pi family] ['q family] ['theta family] ['S nat] ['J nat] (pricing-binder D pi q S J)]
            (eqv (cost pi theta J) (state-value q D theta S J))
            (a/chain (cost pi theta J)
                     [(sum A J) (a/sum-cong (f/lam [['cj nat]] (mul (at pi 'cj) (at theta 'cj))) A J 'pa
                                            (fn [j hj] (mcong (at pi j) (priced q D S j) (at theta j) (at theta j)
                                                              (sym (priced q D S j) (at pi j) (at 'hpi j hj)) (refl (at theta j)))))]
                     [(sum B J) (a/sum-cong A B J 'pb
                                            (fn [j _] (call 'signed/expr-sum-value-scale-right (f/lam [['ps nat]] (mul (at q 'ps) (at D 'ps j))) (at theta j) S)))]
                     [(sum C S) (call 'signed/expr-sum-value-swap T S J)]
                     [(state-value q D theta S J)
                      (a/sum-cong C (f/lam [['vs nat]] (mul (at q 'vs) (payoff D theta J 'vs))) S 'pc
                                  (fn [st _] (let [qs (at q st)]
                                               (a/chain (sum (f/lam [['c2 nat]] (mul (mul qs (at D st 'c2)) (at theta 'c2))) J)
                                                        [(sum (f/lam [['c3 nat]] (mul qs (mul (at D st 'c3) (at theta 'c3)))) J)
                                                         (a/sum-cong (f/lam [['c2 nat]] (mul (mul qs (at D st 'c2)) (at theta 'c2))) (f/lam [['c3 nat]] (mul qs (mul (at D st 'c3) (at theta 'c3)))) J 'pd
                                                                     (fn [j _] (call 'signed/multiply-associative qs (at D st j) (at theta j))))]
                                                        [(mul qs (payoff D theta J st))
                                                         (sym (mul qs (payoff D theta J st)) (sum (f/lam [['c3 nat]] (mul qs (mul (at D st 'c3) (at theta 'c3)))) J)
                                                              (call 'signed/expr-sum-value-scale-left (f/lam [['pj nat]] (mul (at D st 'pj) (at theta 'pj))) qs J))]))))]))))

(defn arb-binders [D q theta S J]
  [['hq (s/all-below S #(le s/zero (at q %)))]
   ['hD (s/all-below S #(le s/zero (payoff D theta J %)))]])

(defn terms-nonneg [D q theta S J]
  (f/lam [['tn nat] ['tn-lt (below 'tn S)]] (nonneg-prod (at q 'tn) (payoff D theta J 'tn) (at 'hq 'tn 'tn-lt) (at 'hD 'tn 'tn-lt))))

(def first-kind-spec
  (let [D 'D pi 'pi q 'q theta 'theta S 'S J 'J V (state-value q D theta S J)]
    (s/spec 'signed/state-price-no-arbitrage
            (into [['D matrix] ['pi family] ['q family] ['theta family] ['S nat] ['J nat] (pricing-binder D pi q S J)] (arb-binders D q theta S J))
            (le s/zero (cost pi theta J))
            (le-resp s/zero s/zero V (cost pi theta J) (refl s/zero)
                     (sym (cost pi theta J) V (call 'signed/state-price-pricing D pi q theta S J 'hpi))
                     (call 'signed/expr-sum-value-nonnegative (f/lam [['vs nat]] (mul (at q 'vs) (payoff D theta J 'vs))) S (terms-nonneg D q theta S J))))))

(def second-kind-spec
  (let [D 'D pi 'pi q 'q theta 'theta S 'S J 'J V (state-value q D theta S J)
        term (mul (at q 's0) (payoff D theta J 's0))
        term-le (call 'signed/expr-sum-value-term-bound (f/lam [['vs nat]] (mul (at q 'vs) (payoff D theta J 'vs))) S (terms-nonneg D q theta S J) 's0 's0-lt)
        pos (call 'signed/less-than-of-less-than-of-at-most s/zero term V (call 'signed/multiply-positive (at q 's0) (payoff D theta J 's0) 'hq0 'hD0) term-le)]
    (s/spec 'signed/state-price-no-arbitrage-strict
            (-> [['D matrix] ['pi family] ['q family] ['theta family] ['S nat] ['J nat] (pricing-binder D pi q S J)]
                (into (arb-binders D q theta S J))
                (into [['s0 nat] ['s0-lt (below 's0 S)] ['hq0 (lt s/zero (at q 's0))] ['hD0 (lt s/zero (payoff D theta J 's0))]]))
            (lt s/zero (cost pi theta J))
            (call 'signed/less-than-of-less-than-of-at-most s/zero V (cost pi theta J) pos
                  (a/eq-le V (cost pi theta J) (sym (cost pi theta J) V (call 'signed/state-price-pricing D pi q theta S J 'hpi)))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "state-price-conditions-" stem)) :accepted (symbol "signed" (str "state-price-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-state-price-" stem))} kind))

(def theorem-specs [pricing-spec first-kind-spec second-kind-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.sums.two-terms rainbow.math.rational.signed.multiply-positive rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-state-price theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.state-price))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
