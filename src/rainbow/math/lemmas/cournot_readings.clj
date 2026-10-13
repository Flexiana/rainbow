(ns rainbow.math.lemmas.cournot-readings
  "General lemmas: cournot readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.add-associative :as add-associative]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
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

(defn pp "the checker's max(0, v): if-at-most 0 v v 0" [v] (sel s/zero v (call 'signed/decide-at-most s/zero v)))

(defn pp-facts [v w] (pconj (le s/zero w) (pconj (le v w) (disj (eqv w s/zero) (eqv w v)))))

(defn eq-le [x y h] (a/eq-le x y h))

(defn pfacts [v w] (pconj (disj (eqv w s/zero) (eqv w v)) (pconj (le s/zero w) (le v w))))

(defn mcong [x xh y yh h k] (call 'signed/multiply-respects-equivalence x xh y yh h k))

(defn acong [x xh y yh h k] (call 'signed/add-respects-equivalence x xh y yh h k))

(defn profit "y ((a - b ((Q - q) + y)) - c)" [a b Q q c y] (mul y (add (add a (neg (mul b (add (sub Q q) y)))) (neg c))))

(defn ring-atoms
  "ring-eq on x ~ y over fresh atoms, applied back to the given terms: [[atom term] ...] (ring-eq's proof
  size explodes with the number of atoms and their degree, so every rearrangement here is over <= 4 atoms)"
  [pairs x y]
  (reduce (fn [t [_ term]] (f/app t term)) (f/lam (mapv (fn [[v _]] [v signed]) pairs) (ring x y)) pairs))

(defn dl [k x y] (call 'signed/multiply-distributes-add-left k x y))

(defn dr [x y m] (call 'signed/multiply-distributes-add-right x y m))

(defn neg-mul [x y] (ring-atoms [['nm-x x] ['nm-y y]] (mul (neg 'nm-x) 'nm-y) (neg (mul 'nm-x 'nm-y))))

(defn mul-neg [x y] (ring-atoms [['mn-x x] ['mn-y y]] (mul 'mn-x (neg 'mn-y)) (neg (mul 'mn-x 'mn-y))))

(defn negc [x y h] (call 'signed/negate-respects-equivalence x y h))

(defn chain "trans along terms ts with proofs hs (each ts_i ~ ts_i+1)" [ts hs]
  (if (= 2 (count ts)) (first hs)
      (trans (first ts) (second ts) (last ts) (first hs) (chain (rest ts) (rest hs)))))

(def best-response-spec
  (let [[a b Q q c P x] '[cb-a cb-b cb-q cb-qi cb-c cb-p cb-x]
        bq (mul b q) bx (mul b x) bQ (mul b Q) M (add bq bq) R (sub Q q)
        ;; the residual intercept m = (a - c) - b R is 2 b q by the first-order condition
        m (add (sub a c) (neg (mul b R))) price (add a (neg bQ)) tail (add (neg bq) (neg c)) F0 (add price tail)
        hF0 (trans F0 (add P tail) s/zero (acong price P tail tail (sym P price 'cb-hp) (refl tail)) 'cb-hf)
        hbR (chain [(mul b R) (add bQ (mul b (neg q))) (add bQ (neg bq))]
                   [(dl b Q (neg q)) (acong bQ bQ (mul b (neg q)) (neg bq) (refl bQ) (mul-neg b q))])
        m1 (add (sub a c) (neg (add bQ (neg bq))))
        hm (chain [m m1 (add M F0) (add M s/zero) M]
                  [(acong (sub a c) (sub a c) (neg (mul b R)) (neg (add bQ (neg bq))) (refl (sub a c)) (negc (mul b R) (add bQ (neg bq)) hbR))
                   (ring-atoms [['cm-a a] ['cm-c c] ['cm-bq bQ] ['cm-b bq]]
                               (add (sub 'cm-a 'cm-c) (neg (add 'cm-bq (neg 'cm-b))))
                               (add (add 'cm-b 'cm-b) (add (add 'cm-a (neg 'cm-bq)) (add (neg 'cm-b) (neg 'cm-c)))))
                   (acong M M F0 s/zero (refl M) hF0)
                   (ring-atoms [['cz-m M]] (add 'cz-m s/zero) 'cz-m)])
        ;; profit(y) ~ y (2 b q - b y)
        reduce-profit
        (fn [y]
          (let [by (mul b y) inner (add (add a (neg (mul b (add R y)))) (neg c)) i1 (add (add a (neg (add (mul b R) by))) (neg c))]
            (mcong y y inner (add M (neg by)) (refl y)
                   (chain [inner i1 (add m (neg by)) (add M (neg by))]
                          [(acong (add a (neg (mul b (add R y)))) (add a (neg (add (mul b R) by))) (neg c) (neg c)
                                  (acong a a (neg (mul b (add R y))) (neg (add (mul b R) by)) (refl a) (negc (mul b (add R y)) (add (mul b R) by) (dl b R y)))
                                  (refl (neg c)))
                           (ring-atoms [['cr-a a] ['cr-r (mul b R)] ['cr-y by] ['cr-c c]]
                                       (add (add 'cr-a (neg (add 'cr-r 'cr-y))) (neg 'cr-c))
                                       (add (add (sub 'cr-a 'cr-c) (neg 'cr-r)) (neg 'cr-y)))
                           (acong m M (neg by) (neg by) hm (refl (neg by)))]))))
        px (profit a b Q q c x) pq (profit a b Q q c q)
        px' (mul x (add M (neg bx))) pq' (mul q (add M (neg bq)))
        Q2 (mul q bq) X2 (mul x bx) QX (mul q bx) XQ (mul x bq)
        ;; the three expansions
        eq (chain [pq' (add (mul q M) (mul q (neg bq))) (add (add Q2 Q2) (neg Q2))]
                  [(dl q M (neg bq)) (acong (mul q M) (add Q2 Q2) (mul q (neg bq)) (neg Q2) (dl q bq bq) (mul-neg q bq))])
        ex (chain [px' (add (mul x M) (mul x (neg bx))) (add (add XQ XQ) (neg X2))]
                  [(dl x M (neg bx)) (acong (mul x M) (add XQ XQ) (mul x (neg bx)) (neg X2) (dl x bq bq) (mul-neg x bx))])
        t (sub q x) BT (add bq (neg bx)) bt (mul b t)
        hbt (chain [bt (add bq (mul b (neg x))) BT] [(dl b q (neg x)) (acong bq bq (mul b (neg x)) (neg bx) (refl bq) (mul-neg b x))])
        hxbt (chain [(mul x BT) (add XQ (mul x (neg bx))) (add XQ (neg X2))] [(dl x bq (neg bx)) (acong XQ XQ (mul x (neg bx)) (neg X2) (refl XQ) (mul-neg x bx))])
        hqbt (chain [(mul q BT) (add Q2 (mul q (neg bx))) (add Q2 (neg QX))] [(dl q bq (neg bx)) (acong Q2 Q2 (mul q (neg bx)) (neg QX) (refl Q2) (mul-neg q bx))])
        hqx (chain [QX (mul (mul q b) x) (mul bq x) XQ]
                   [(sym (mul (mul q b) x) QX (call 'signed/multiply-associative q b x))
                    (mcong (mul q b) bq x x (call 'signed/multiply-commutative q b) (refl x))
                    (call 'signed/multiply-commutative bq x)])
        S1 (add (add Q2 (neg QX)) (neg (add XQ (neg X2)))) S2 (add (add Q2 (neg XQ)) (neg (add XQ (neg X2))))
        s' (mul b (mul t t)) tbt (mul t bt)
        es (chain [s' (mul bt t) tbt (mul t BT) (add (mul q BT) (mul (neg x) BT)) S1 S2]
                  [(sym (mul bt t) s' (call 'signed/multiply-associative b t t))
                   (call 'signed/multiply-commutative bt t)
                   (mcong t t bt BT (refl t) hbt)
                   (dr q (neg x) BT)
                   (acong (mul q BT) (add Q2 (neg QX)) (mul (neg x) BT) (neg (add XQ (neg X2))) hqbt
                          (trans (mul (neg x) BT) (neg (mul x BT)) (neg (add XQ (neg X2))) (neg-mul x BT) (negc (mul x BT) (add XQ (neg X2)) hxbt)))
                   (acong (add Q2 (neg QX)) (add Q2 (neg XQ)) (neg (add XQ (neg X2))) (neg (add XQ (neg X2)))
                          (acong Q2 Q2 (neg QX) (neg XQ) (refl Q2) (negc QX XQ hqx)) (refl (neg (add XQ (neg X2)))))])
        ;; pq ~ s' + px
        hq (chain [pq pq' (add (add Q2 Q2) (neg Q2)) (add (add (add XQ XQ) (neg X2)) S2) (add px' S2) (add px' s') (add s' px')]
                  [(reduce-profit q) eq
                   (ring-atoms [['cf-q Q2] ['cf-p XQ] ['cf-x X2]]
                               (add (add 'cf-q 'cf-q) (neg 'cf-q))
                               (add (add (add 'cf-p 'cf-p) (neg 'cf-x)) (add (add 'cf-q (neg 'cf-p)) (neg (add 'cf-p (neg 'cf-x))))))
                   (acong (add (add XQ XQ) (neg X2)) px' S2 S2 (sym px' (add (add XQ XQ) (neg X2)) ex) (refl S2))
                   (acong px' px' S2 s' (refl px') (sym s' S2 es))
                   (call 'signed/add-commutative px' s')])
        hs (nn-prod b (mul t t) 'cb-hb (call 'signed/zero-at-most-of-nonnegative (mul t t) (call 'signed/square-nonnegative t)))
        h1 (call 'signed/add-right-monotone s/zero s' px' hs)
        h0 (trans (add s/zero px') px' px (ring-atoms [['c0-v px']] (add s/zero 'c0-v) 'c0-v) (sym px px' (reduce-profit x)))]
    (s/spec 'signed/cournot-best-response
            [[a signed] [b signed] [Q signed] [q signed] [c signed] [P signed] [x signed]
             ['cb-hp (eqv P price)] ['cb-hf (eqv (add P tail) s/zero)] ['cb-hb (le s/zero b)]]
            (le px pq)
            (le-resp (add s/zero px') px (add s' px') pq h0 (sym pq (add s' px') hq) h1))))

(defn best-response [a b Q q c P x hp hf hb] (call 'signed/cournot-best-response a b Q q c P x hp hf hb))

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

(def theorem-specs [best-response-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-cournot-readings [hhi/positive-spec]) (support/extend-with-shared :expr-sum-cournot-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.cournot-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
