(ns rainbow.math.lemmas.gilmore-pricing
  "General lemmas: gilmore pricing. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le eqv refl sym]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.lp-ray :as ray]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(defn lt [x y] (call 'signed/less-than x y))

(def negative-difference-spec
  (let [positive (a/sub 'value 'unit) negative (a/sub 'unit 'value)
        eqzero (eqv s/zero positive)
        notzero (call 'proposition/negation eqzero)
        hnonzero (call 'proposition/right (le s/zero positive) notzero 'positive)
        reversed (call 'signed/negate-reverses-order s/zero positive
                   (call 'signed/less-than-implies-at-most s/zero positive 'positive))
        nn (s/le-transport (a/neg positive) negative (a/neg s/zero) s/zero
             (a/ring-eq (a/neg positive) negative) (a/ring-eq (a/neg s/zero) s/zero) reversed)
        nonzero (f/lam [['eqzero (eqv negative s/zero)]]
                  (f/app hnonzero
                    (a/chain s/zero
                      [(a/neg s/zero) (a/ring-eq s/zero (a/neg s/zero))]
                      [(a/neg negative) (a/neg-cong s/zero negative (sym negative s/zero 'eqzero))]
                      [positive (a/ring-eq (a/neg negative) positive)])))]
    (s/spec 'signed/positive-difference-negative-reverse
      [['value signed] ['unit signed] ['positive (lt s/zero positive)]]
      (lt negative s/zero)
      (call 'signed/less-than-intro negative s/zero nn nonzero))))

(defn pattern [A j] (f/lam [['item nat]] (at A 'item j)))

(defn all-pricing [w W prices m]
  (f/forall [['pattern family] ['counts (lp/nonnegative 'pattern m)]
             ['capacity (le (lp/objective 'pattern w m) W)]]
    (le (lp/objective 'pattern prices m) b/one)))

(defn pricing-bindings []
  [['A lp/matrix] ['d family] ['w family] ['W signed] ['prices family] ['x family] ['m nat] ['n nat]
   ['prices-nonnegative (lp/nonnegative 'prices 'm)]
   ['all-pricing (all-pricing 'w 'W 'prices 'm)]
   ['pattern-counts (f/forall [['column nat] ['hc (s/below 'column 'n)]] (lp/nonnegative (pattern 'A 'column) 'm))]
   ['pattern-capacity (s/all-below 'n #(le (lp/objective (pattern 'A %) 'w 'm) 'W))]
   ['cover (b/covering 'A 'd 'x 'm 'n)] ['nonnegative (lp/nonnegative 'x 'n)]])

(def pricing-bound-spec
  (let [ones (f/lam [['column nat]] b/one)
        lhs (lp/objective 'd 'prices 'm) rhs (lp/objective ones 'x 'n)
        dual (f/lam [['column nat] ['hc (s/below 'column 'n)]]
               (at 'all-pricing (pattern 'A 'column) (at 'pattern-counts 'column 'hc)
                 (at 'pattern-capacity 'column 'hc)))]
    (s/spec 'signed/gilmore-complete-pricing-cover-bound (pricing-bindings)
      (le lhs (sum 'x 'n))
      (s/le-transport lhs lhs rhs (sum 'x 'n) (refl lhs)
        (call 'signed/expr-sum-unit-objective 'x 'n)
        (call 'signed/expr-sum-covering-weak-duality 'A 'd ones 'x 'prices 'm 'n
          'cover 'nonnegative 'prices-nonnegative dual)))))

(def theorem-specs [negative-difference-spec pricing-bound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.lp-duality rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.lp-bounds rainbow.math.lemmas.lp-farkas rainbow.math.lemmas.lp-ray])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-gilmore-pricing theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.gilmore-pricing))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
