(ns rainbow.math.lemmas.abc-class
  "General lemmas: abc class. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn strict-ind [x y] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) one s/zero (call 'signed/decide-at-most y x)))

(defn sel [t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) one s/zero t))

(def strict-nonneg-spec
  (let [x 'sn-x y 'sn-y]
    (s/spec 'signed/strict-indicator-nonnegative [['sn-x signed] ['sn-y signed]]
            (le s/zero (strict-ind x y))
            (f/app (f/const* 'data/Bool.rec [prop-level])
                   (f/lam [['sn-b bool]] (le s/zero (sel 'sn-b)))
                   zero-le-one
                   (call 'signed/at-most-reflexive s/zero)
                   (call 'signed/decide-at-most y x)))))

(def strict-zero-spec
  (let [x 'sz-x y 'sz-y D (call 'signed/decide-at-most y x)
        eqb (fn [t] (f/equality type-level bool D t))
        claim (fn [t] (f/forall [['sz-e (eqb t)] ['sz-h (eqv (sel t) s/zero)]] (le y x)))]
    (s/spec 'signed/strict-indicator-zero-order [['sz-x signed] ['sz-y signed] ['sz-h0 (eqv (strict-ind x y) s/zero)]]
            (le y x)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['sz-b bool]] (claim 'sz-b))
                          ;; decided false: the indicator is 1, and 1 ~ 0 is impossible
                          (f/lam [['sz-e (eqb (f/const* 'data/false []))] ['sz-h (eqv one s/zero)]]
                                 (call 'proposition/explode (le y x) (call 'signed/one-not-equivalent-zero 'sz-h)))
                          (f/lam [['sz-e (eqb (f/const* 'data/true []))] ['sz-h (eqv s/zero s/zero)]]
                                 (call 'signed/decide-at-most-true-sound y x 'sz-e))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)
                   'sz-h0))))

(defn row [v z n i] (sum (f/lam [['rw-j nat]] (mul (sub one (at z 'rw-j)) (strict-ind (at v i) (at v 'rw-j)))) n))

(def dominates-spec
  (let [v 'dm-v z 'dm-z n 'dm-n i 'dm-i j 'dm-j vi (at v i) vj (at v j) zi (at z i) zj (at z j)
        R (row v z n i)
        T (f/lam [['rw-j nat]] (mul (sub one (at z 'rw-j)) (strict-ind vi (at v 'rw-j))))
        r0 (a/chain R [(mul one R) (sym (mul one R) R (one-times R))]
                    [(mul zi R) (mcong one zi R R (sym zi one 'dm-zi) (refl R))]
                    [s/zero (at 'dm-top i 'dm-hi)])
        tnn (f/lam [['tn-j nat] ['tn-h (below 'tn-j n)]]
                   (nonneg-prod (sub one (at z 'tn-j)) (strict-ind vi (at v 'tn-j))
                                (call 'signed/one-minus-nonnegative (at z 'tn-j) (call 'signed/zero-one-at-most-one (at z 'tn-j) (at 'dm-01 'tn-j 'tn-h)))
                                (call 'signed/strict-indicator-nonnegative vi (at v 'tn-j))))
        each (call 'signed/expr-sum-value-nonnegative-terms-zero T n tnn r0)
        I (strict-ind vi vj)
        I0 (a/chain I [(mul one I) (sym (mul one I) I (one-times I))]
                    [(mul (sub one s/zero) I) (mcong one (sub one s/zero) I I (ring one (sub one s/zero)) (refl I))]
                    [(mul (sub one zj) I) (mcong (sub one s/zero) (sub one zj) I I
                                                 (s/add-cong one one (neg s/zero) (neg zj) (refl one) (a/neg-cong s/zero zj (sym zj s/zero 'dm-zj)))
                                                 (refl I))]
                    [s/zero (at each j 'dm-hj)])]
    (s/spec 'signed/abc-selected-dominates
            [['dm-v family] ['dm-z family] ['dm-n nat]
             ['dm-01 (s/all-below n #(zero-one (at z %)))]
             ['dm-top (s/all-below n #(eqv (mul (at z %) (row v z n %)) s/zero))]
             ['dm-i nat] ['dm-hi (below i n)] ['dm-j nat] ['dm-hj (below j n)]
             ['dm-zi (eqv zi one)] ['dm-zj (eqv zj s/zero)]]
            (le vj vi)
            (call 'signed/strict-indicator-zero-order vi vj I0))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec indep/zero-one-upper-spec indep/one-minus-spec indep/subtract-expand-spec])

(def theorem-specs [strict-nonneg-spec strict-zero-spec dominates-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-abc-class borrowed-specs) (support/extend-with-shared :expr-sum-abc-class theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.abc-class))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
