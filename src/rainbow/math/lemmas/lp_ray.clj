(ns rainbow.math.lemmas.lp-ray
  "General lemmas: lp ray. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le eqv refl sym]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.lemmas.lp-farkas :as farkas]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
            [rainbow.math.lemmas.indep-set-dual :as order]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(defn ray [x d t] (f/lam [['ray-index nat]] (add (at x 'ray-index) (mul t (at d 'ray-index)))))

(def affine-spec
  (let [lhs (lp/objective 'c (ray 'x 'd 't) 'n)
        cx (lp/products 'c 'x) cd (lp/products 'c 'd)
        scaled (f/lam [['j nat]] (mul 't (at cd 'j)))
        added (f/lam [['j nat]] (add (at cx 'j) (at scaled 'j)))
        rhs (add (sum cx 'n) (mul 't (sum cd 'n)))]
    (s/spec 'signed/expr-sum-ray-objective [['c family] ['x family] ['d family] ['t signed] ['n nat]]
      (eqv lhs rhs)
      (a/chain lhs
        [(sum added 'n) (a/sum-cong (lp/products 'c (ray 'x 'd 't)) added 'n 'j
                         (fn [j _] (a/ring-eq (mul (at 'c j) (add (at 'x j) (mul 't (at 'd j))))
                                      (add (mul (at 'c j) (at 'x j)) (mul 't (mul (at 'c j) (at 'd j)))))))]
        [(add (sum cx 'n) (sum scaled 'n)) (call 'signed/expr-sum-value-add cx scaled 'n)]
        [rhs (s/add-cong (sum cx 'n) (sum cx 'n) (sum scaled 'n) (mul 't (sum cd 'n)) (refl (sum cx 'n))
               (sym (mul 't (sum cd 'n)) (sum scaled 'n) (call 'signed/expr-sum-value-scale-left cd 't 'n)))]))))

(defn ray-conclusions [A rhs c x d t m n]
  [(lp/nonnegative (ray x d t) n) (lp/primal-feasible A rhs (ray x d t) m n)
   (eqv (lp/objective c (ray x d t) n) (add (lp/objective c x n) (mul t (lp/objective c d n))))])

(def feasible-spec
  (let [point (ray 'x 'd 't)
        nonnegative (f/lam [['j nat] ['hj (s/below 'j 'n)]]
                      (let [xj (at 'x 'j) dj (at 'd 'j) td (mul 't dj)
                            product (s/le-transport (mul 't s/zero) s/zero td td
                                      (call 'signed/multiply-zero-right 't) (refl td)
                                      (call 'signed/multiply-left-monotone 't s/zero dj 'tn (at 'dn 'j 'hj)))]
                        (s/le-transport (add s/zero s/zero) s/zero (add xj td) (add xj td)
                          (a/ring-eq (add s/zero s/zero) s/zero) (refl (add xj td))
                          (call 'signed/add-monotone s/zero xj s/zero td (at 'xn 'j 'hj) product))))
        feasible (f/lam [['i nat] ['hi (s/below 'i 'm)]]
                   (let [row (f/lam [['j nat]] (at 'A 'i 'j))
                         ax (lp/row 'A 'x 'n 'i) ad (lp/row 'A 'd 'n 'i) rhs (at 'b 'i)
                         tad (mul 't ad) ar (lp/row 'A point 'n 'i)
                         direction (s/le-transport tad tad (mul 't s/zero) s/zero (refl tad)
                                     (call 'signed/multiply-zero-right 't)
                                     (call 'signed/multiply-left-monotone 't ad s/zero 'tn (at 'direction 'i 'hi)))]
                     (s/le-transport (add ax tad) ar (add rhs s/zero) rhs
                       (sym ar (add ax tad) (call 'signed/expr-sum-ray-objective row 'x 'd 't 'n))
                       (a/ring-eq (add rhs s/zero) rhs)
                       (call 'signed/add-monotone ax rhs tad s/zero (at 'primal 'i 'hi) direction))))
        goals (ray-conclusions 'A 'b 'c 'x 'd 't 'm 'n)]
    (s/spec 'signed/expr-sum-lp-feasible-ray
      [['A lp/matrix] ['b family] ['c family] ['x family] ['d family] ['t signed] ['m nat] ['n nat]
       ['primal (lp/primal-feasible 'A 'b 'x 'm 'n)] ['xn (lp/nonnegative 'x 'n)]
       ['direction (lp/primal-feasible 'A farkas/zeros 'd 'm 'n)] ['dn (lp/nonnegative 'd 'n)] ['tn (le s/zero 't)]]
      (b/conjunction goals)
      (b/conjoin goals [nonnegative feasible (call 'signed/expr-sum-ray-objective 'c 'x 'd 't 'n)]))))

(def borrowed-specs [order/total-spec hhi/positive-spec])

(def theorem-specs [affine-spec feasible-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.lp-duality rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.lp-bounds rainbow.math.lemmas.lp-farkas])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-lp-ray borrowed-specs) (support/extend-with :expr-sum-lp-ray theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.lp-ray))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
