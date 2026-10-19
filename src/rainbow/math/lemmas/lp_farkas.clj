(ns rainbow.math.lemmas.lp-farkas
  "General lemmas: lp farkas. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(def zeros (f/lam [['j nat]] s/zero))

(def zero-objective-spec
  (s/spec 'signed/expr-sum-zero-objective [['x family] ['n nat]]
    (eqv (lp/objective zeros 'x 'n) s/zero)
    (s/trans (lp/objective zeros 'x 'n) (sum zeros 'n) s/zero
      (a/sum-cong (lp/products zeros 'x) zeros 'n 'j
        (fn [j _] (call 'signed/multiply-zero-left (at 'x j))))
      (call 'signed/expr-sum-value-zero 'n))))

(def nonnegative-spec
  (let [value (lp/objective 'b 'y 'm)]
    (s/spec 'signed/expr-sum-lp-farkas-nonnegative
      [['A lp/matrix] ['b family] ['x family] ['y family] ['m nat] ['n nat]
       ['primal (lp/primal-feasible 'A 'b 'x 'm 'n)] ['xn (lp/nonnegative 'x 'n)]
       ['yn (lp/nonnegative 'y 'm)] ['dual (lp/dual-feasible 'A zeros 'y 'm 'n)]]
      (le s/zero value)
      (s/le-transport (lp/objective zeros 'x 'n) s/zero value value
        (call 'signed/expr-sum-zero-objective 'x 'n) (refl value)
        (call 'signed/expr-sum-lp-weak-duality 'A 'b zeros 'x 'y 'm 'n 'primal 'xn 'yn 'dual)))))

(def theorem-specs [zero-objective-spec nonnegative-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.lp-duality rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.lp-bounds])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-lp-farkas theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.lp-farkas))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
