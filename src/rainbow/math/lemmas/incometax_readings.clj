(ns rainbow.math.lemmas.incometax-readings
  "General lemmas: incometax readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.fulfil-readings :as ful]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
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

(defn tsel "the checker's taxable income: if-at-most g A 0 (g - A)" [g A] (sel (sub g A) s/zero (call 'signed/decide-at-most g A)))

(defn allow-facts [g A t] (pconj (le s/zero t) (pconj (le (sub g A) t) (pconj (disj (eqv t s/zero) (eqv t (sub g A))) (le t g)))))

(def allow-spec
  (let [g 'al-g A 'al-A t 'al-t u (sub g A) D (call 'signed/decide-at-most g A)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['al-de (eqb b)] ['al-ht (eqv t (sel u s/zero b))]] (allow-facts g A t)))
        Or (disj (eqv t s/zero) (eqv t u))
        u-le-g (le-resp (add (neg A) g) u (add (neg s/zero) g) g (ring (add (neg A) g) u) (ring (add (neg s/zero) g) g)
                        (call 'signed/add-right-monotone (neg A) (neg s/zero) g (call 'signed/negate-reverses-order s/zero A 'al-hA)))
        pack (fn [nn lo orr tg]
               (conjoin (le s/zero t) (pconj (le u t) (pconj Or (le t g))) nn
                        (conjoin (le u t) (pconj Or (le t g)) lo (conjoin Or (le t g) orr tg))))]
    (s/spec 'signed/allowance-cases [['al-g signed] ['al-A signed] ['al-t signed] ['al-hg (le s/zero g)] ['al-hA (le s/zero A)]
                                     ['al-ht (eqv t (tsel g A))]]
            (allow-facts g A t)
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['al-b bool]] (claim 'al-b))
                          ;; decided false: A <= g, t ~ g - A
                          (f/lam [['al-de (eqb (f/const* 'data/false []))] ['al-ht (eqv t u)]]
                                 (let [A-g (call 'signed/decide-at-most-false-reverse g A 'al-de)]
                                   (pack (le-resp s/zero s/zero u t (refl s/zero) (sym t u 'al-ht) (diff-nn A g A-g))
                                         (a/eq-le u t (sym t u 'al-ht))
                                         (inr (eqv t s/zero) (eqv t u) 'al-ht)
                                         (le-resp u t g g (sym t u 'al-ht) (refl g) u-le-g))))
                          ;; decided true: g <= A, t ~ 0
                          (f/lam [['al-de (eqb (f/const* 'data/true []))] ['al-ht (eqv t s/zero)]]
                                 (let [g-A (call 'signed/decide-at-most-true-sound g A 'al-de)
                                       u-np (le-resp (sub g A) u (sub A A) s/zero (refl u) (ring (sub A A) s/zero)
                                                     (call 'signed/add-right-monotone g A (neg A) g-A))]
                                   (pack (a/eq-le s/zero t (sym t s/zero 'al-ht))
                                         (le-resp u u s/zero t (refl u) (sym t s/zero 'al-ht) u-np)
                                         (inl (eqv t s/zero) (eqv t u) 'al-ht)
                                         (le-resp s/zero t g g (sym t s/zero 'al-ht) (refl g) 'al-hg))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D) 'al-ht))))

(defn cell-facts [g A B t b h x]
  (pconj (allow-facts g A t)
         (pconj (pconj (disj (eqv b t) (eqv b B)) (pconj (le b t) (le b B)))
                (pconj (pconj (le s/zero h) (disj (eqv h s/zero) (eqv b B))) (le s/zero x)))))

(def cell-spec
  (let [g 'tx-g A 'tx-A B 'tx-B r1 'tx-r1 r2 'tx-r2 t 'tx-t b 'tx-b h 'tx-h x 'tx-x
        fst (fn [P Q hh] (call 'proposition/left P Q hh)) snd (fn [P Q hh] (call 'proposition/right P Q hh))
        af (call 'signed/allowance-cases g A t 'tx-hg 'tx-hA 'tx-ht)
        Or (disj (eqv t s/zero) (eqv t (sub g A)))
        t-nn (fst (le s/zero t) (pconj (le (sub g A) t) (pconj Or (le t g))) af)
        v (ful/msel t B) mf (call 'signed/min-select-cases t B)
        sb (sym b v 'tx-hb)
        v-t (fst (le v t) (pconj (le v B) (disj (eqv v t) (eqv v B))) mf)
        v-B (fst (le v B) (disj (eqv v t) (eqv v B)) (snd (le v t) (pconj (le v B) (disj (eqv v t) (eqv v B))) mf))
        v-or (snd (le v B) (disj (eqv v t) (eqv v B)) (snd (le v t) (pconj (le v B) (disj (eqv v t) (eqv v B))) mf))
        b-t (le-resp v b t t sb (refl t) v-t)
        b-B (le-resp v b B B sb (refl B) v-B)
        b-or (cases (eqv v t) (eqv v B) (disj (eqv b t) (eqv b B)) v-or
                    (f/lam [['tx-vt (eqv v t)]] (inl (eqv b t) (eqv b B) (trans b v t 'tx-hb 'tx-vt)))
                    (f/lam [['tx-vB (eqv v B)]] (inr (eqv b t) (eqv b B) (trans b v B 'tx-hb 'tx-vB))))
        b-nn (cases (eqv b t) (eqv b B) (le s/zero b) b-or
                    (f/lam [['tx-bt (eqv b t)]] (le-resp s/zero s/zero t b (refl s/zero) (sym b t 'tx-bt) t-nn))
                    (f/lam [['tx-bB (eqv b B)]] (le-resp s/zero s/zero B b (refl s/zero) (sym b B 'tx-bB) 'tx-hB)))
        h-nn (le-resp s/zero s/zero (sub t b) h (refl s/zero) (sym h (sub t b) 'tx-hh) (diff-nn b t b-t))
        h-or (cases (eqv b t) (eqv b B) (disj (eqv h s/zero) (eqv b B)) b-or
                    (f/lam [['tx-bt (eqv b t)]]
                           (inl (eqv h s/zero) (eqv b B)
                                (a/chain h [(sub t b) 'tx-hh] [(sub t t) (s/add-cong t t (neg b) (neg t) (refl t) (a/neg-cong b t 'tx-bt))]
                                         [s/zero (ring (sub t t) s/zero)])))
                    (f/lam [['tx-bB (eqv b B)]] (inr (eqv h s/zero) (eqv b B) 'tx-bB)))
        p (mul r1 b) q (mul r2 h)
        x-nn (le-resp (add s/zero s/zero) s/zero (add p q) x (ring (add s/zero s/zero) s/zero) (sym x (add p q) 'tx-hx)
                      (le-trans (add s/zero s/zero) (add p s/zero) (add p q)
                                (call 'signed/add-right-monotone s/zero p s/zero (nn-prod r1 b 'tx-hr1 b-nn))
                                (le-resp (add s/zero p) (add p s/zero) (add q p) (add p q) (ring (add s/zero p) (add p s/zero)) (ring (add q p) (add p q))
                                         (call 'signed/add-right-monotone s/zero q p (nn-prod r2 h 'tx-hr2 h-nn)))))
        Bpart (pconj (disj (eqv b t) (eqv b B)) (pconj (le b t) (le b B)))
        Hpart (pconj (pconj (le s/zero h) (disj (eqv h s/zero) (eqv b B))) (le s/zero x))]
    (s/spec 'signed/tax-cell
            [['tx-g signed] ['tx-A signed] ['tx-B signed] ['tx-r1 signed] ['tx-r2 signed] ['tx-t signed] ['tx-b signed] ['tx-h signed] ['tx-x signed]
             ['tx-hg (le s/zero g)] ['tx-hA (le s/zero A)] ['tx-hB (le s/zero B)] ['tx-hr1 (le s/zero r1)] ['tx-hr2 (le s/zero r2)]
             ['tx-ht (eqv t (tsel g A))] ['tx-hb (eqv b v)] ['tx-hh (eqv h (sub t b))] ['tx-hx (eqv x (add p q))]]
            (cell-facts g A B t b h x)
            (conjoin (allow-facts g A t) (pconj Bpart Hpart) af
                     (conjoin Bpart Hpart
                              (conjoin (disj (eqv b t) (eqv b B)) (pconj (le b t) (le b B)) b-or (conjoin (le b t) (le b B) b-t b-B))
                              (conjoin (pconj (le s/zero h) (disj (eqv h s/zero) (eqv b B))) (le s/zero x)
                                       (conjoin (le s/zero h) (disj (eqv h s/zero) (eqv b B)) h-nn h-or) x-nn))))))

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

(def theorem-specs [allow-spec cell-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-incometax-readings [ful/min-select-spec]) (support/extend-with-shared :expr-sum-incometax-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.incometax-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
