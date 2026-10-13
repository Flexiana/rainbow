(ns rainbow.math.lemmas.dc-power-flow
  "General lemmas: dc power flow. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn assoc* [x y z] (call 'signed/multiply-associative x y z))

(defn balance [A f m i] (sum (f/lam [['bl nat]] (mul (at A 'bl i) (at f 'bl))) m))

(defn row-sum [A n l] (sum (f/lam [['ri nat]] (at A l 'ri)) n))

(defn angle-sum [A theta n l] (sum (f/lam [['aj nat]] (mul (at A l 'aj) (at theta 'aj))) n))

(defn susceptance [A B m i j] (sum (f/lam [['yl nat]] (mul (mul (at A 'yl i) (at B 'yl)) (at A 'yl j))) m))

(defn nodal [A B theta n m i] (sum (f/lam [['nj nat]] (mul (susceptance A B m i 'nj) (at theta 'nj))) n))

(defn hbal [A f p n m] ['hbal (s/all-below n #(eqv (at p %) (balance A f m %)))])

(def conserved-spec
  (let [A 'A f 'f p 'p n 'n m 'm
        byBus (f/lam [['cb nat]] (balance A f m 'cb))
        T (f/lam [['ti nat] ['tl nat]] (mul (at A 'tl 'ti) (at f 'tl)))
        byLine (f/lam [['cl nat]] (sum (f/lam [['ci nat]] (mul (at A 'cl 'ci) (at f 'cl))) n))
        scaled (f/lam [['cs nat]] (mul (row-sum A n 'cs) (at f 'cs)))
        Z (f/lam [['cz nat]] s/zero)]
    (s/spec 'signed/incidence-balance-conserved
            [['A matrix] ['f family] ['p family] ['n nat] ['m nat]
             ['hrow (s/all-below m #(eqv (row-sum A n %) s/zero))] (hbal A f p n m)]
            (eqv (sum (f/lam [['cp nat]] (at p 'cp)) n) s/zero)
            (a/chain (sum (f/lam [['cp nat]] (at p 'cp)) n)
                     [(sum byBus n) (a/sum-cong (f/lam [['cp nat]] (at p 'cp)) byBus n 'ca (fn [i hi] (at 'hbal i hi)))]
                     [(sum byLine m) (call 'signed/expr-sum-value-swap T m n)]
                     [(sum scaled m) (a/sum-cong byLine scaled m 'cc
                                                 (fn [l _] (sym (mul (row-sum A n l) (at f l)) (sum (f/lam [['ci nat]] (mul (at A l 'ci) (at f l))) n)
                                                                (call 'signed/expr-sum-value-scale-right (f/lam [['ri nat]] (at A l 'ri)) (at f l) n))))]
                     [(sum Z m) (a/sum-cong scaled Z m 'cd
                                            (fn [l hl] (trans (mul (row-sum A n l) (at f l)) (mul s/zero (at f l)) s/zero
                                                              (mcong (row-sum A n l) s/zero (at f l) (at f l) (at 'hrow l hl) (refl (at f l)))
                                                              (call 'signed/multiply-zero-left (at f l)))))]
                     [s/zero (call 'signed/expr-sum-value-zero m)]))))

(def susceptance-spec
  (let [A 'A B 'B f 'f p 'p theta 'theta n 'n m 'm i 'i
        K (fn [l j] (mul (mul (mul (at A l i) (at B l)) (at A l j)) (at theta j)))
        byLine (f/lam [['sl nat]] (sum (f/lam [['sj nat]] (K 'sl 'sj)) n))
        byBus (f/lam [['sb nat]] (sum (f/lam [['sk nat]] (K 'sk 'sb)) m))
        subst-flow (f/lam [['sf nat]] (mul (at A 'sf i) (mul (at B 'sf) (angle-sum A theta n 'sf))))
        per-line (fn [l]
                   (let [a (at A l i) b (at B l) S (angle-sum A theta n l) ab (mul a b)]
                     (a/chain (mul a (mul b S))
                              [(mul ab S) (sym (mul ab S) (mul a (mul b S)) (assoc* a b S))]
                              [(sum (f/lam [['pj nat]] (mul ab (mul (at A l 'pj) (at theta 'pj)))) n)
                               (call 'signed/expr-sum-value-scale-left (f/lam [['aj nat]] (mul (at A l 'aj) (at theta 'aj))) ab n)]
                              [(sum (f/lam [['sj nat]] (K l 'sj)) n)
                               (a/sum-cong (f/lam [['pj nat]] (mul ab (mul (at A l 'pj) (at theta 'pj)))) (f/lam [['sj nat]] (K l 'sj)) n 'pk
                                           (fn [j _] (sym (K l j) (mul ab (mul (at A l j) (at theta j))) (assoc* ab (at A l j) (at theta j)))))])))]
    (s/spec 'signed/incidence-balance-susceptance
            [['A matrix] ['B family] ['f family] ['p family] ['theta family] ['n nat] ['m nat]
             ['hflow (s/all-below m #(eqv (at f %) (mul (at B %) (angle-sum A theta n %))))] (hbal A f p n m)
             ['i nat] ['i-lt (below 'i n)]]
            (eqv (at p i) (nodal A B theta n m i))
            (a/chain (at p i)
                     [(balance A f m i) (at 'hbal i 'i-lt)]
                     [(sum subst-flow m) (a/sum-cong (f/lam [['bl nat]] (mul (at A 'bl i) (at f 'bl))) subst-flow m 'sa
                                                     (fn [l hl] (mcong (at A l i) (at A l i) (at f l) (mul (at B l) (angle-sum A theta n l)) (refl (at A l i)) (at 'hflow l hl))))]
                     [(sum byLine m) (a/sum-cong subst-flow byLine m 'sc (fn [l _] (per-line l)))]
                     [(sum byBus n) (call 'signed/expr-sum-value-swap (f/lam [['tl nat] ['tj nat]] (K 'tl 'tj)) n m)]
                     [(nodal A B theta n m i)
                      (a/sum-cong byBus (f/lam [['nj nat]] (mul (susceptance A B m i 'nj) (at theta 'nj))) n 'sd
                                  (fn [j _] (sym (mul (susceptance A B m i j) (at theta j)) (sum (f/lam [['sk nat]] (K 'sk j)) m)
                                                 (call 'signed/expr-sum-value-scale-right (f/lam [['yl nat]] (mul (mul (at A 'yl i) (at B 'yl)) (at A 'yl j))) (at theta j) m))))]))))

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

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn both-ways [G k1 k2 n lhs rhs]
  (f/lam [['bw nat] ['bw-lt (below 'bw n)]] (anti (lhs 'bw) (rhs 'bw) (at (G k1) 'bw 'bw-lt) (at (G k2) 'bw 'bw-lt))))

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "dcpf-conditions-" stem)) :accepted (symbol "signed" (str "dcpf-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-dcpf-" stem))} kind))

(def theorem-specs [conserved-spec susceptance-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-dc-power-flow theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.dc-power-flow))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
