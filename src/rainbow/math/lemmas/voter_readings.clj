(ns rainbow.math.lemmas.voter-readings
  "General lemmas: voter readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.fulfil-readings :as ful]
            [rainbow.math.lemmas.nsfr-reading :as nsfr]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
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

(defn mn [x y] (ful/msel x y))

(defn mx "the checker's max(x, y): if-at-most x y y x" [x y] (sel x y (call 'signed/decide-at-most x y)))

(defn max-facts [x y v] (pconj (le x v) (pconj (le y v) (disj (eqv v x) (eqv v y)))))

(def max-select-spec
  (let [x 'mz-x y 'mz-y D (call 'signed/decide-at-most x y)
        eqb (fn [b] (f/equality type-level bool D b))
        claim (fn [b] (f/forall [['mz-e (eqb b)]] (max-facts x y (sel x y b))))]
    (s/spec 'signed/max-select-cases [['mz-x signed] ['mz-y signed]]
            (max-facts x y (mx x y))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['mz-b bool]] (claim 'mz-b))
                          ;; decided false: y <= x, value x
                          (f/lam [['mz-e (eqb (f/const* 'data/false []))]]
                                 (conjoin (le x x) (pconj (le y x) (disj (eqv x x) (eqv x y))) (a/eq-le x x (refl x))
                                          (conjoin (le y x) (disj (eqv x x) (eqv x y)) (call 'signed/decide-at-most-false-reverse x y 'mz-e)
                                                   (inl (eqv x x) (eqv x y) (refl x)))))
                          ;; decided true: x <= y, value y
                          (f/lam [['mz-e (eqb (f/const* 'data/true []))]]
                                 (conjoin (le x y) (pconj (le y y) (disj (eqv y x) (eqv y y))) (call 'signed/decide-at-most-true-sound x y 'mz-e)
                                          (conjoin (le y y) (disj (eqv y x) (eqv y y)) (a/eq-le y y (refl y)) (inr (eqv y x) (eqv y y) (refl y)))))
                          D)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

(defn med [x y z] (mx (mn x y) (mn (mx x y) z)))

(defn spr [x y z] (sub (mx x (mx y z)) (mn x (mn y z))))

(defn cell-facts [x y z m sv fv T]
  (pconj (disj (eqv m x) (disj (eqv m y) (eqv m z)))
         (pconj (le (mn x y) m) (pconj (le m (mx x y)) (pconj (le s/zero sv) (nsfr/reading sv T fv))))))

(def cell-spec
  (let [x 'vc-a y 'vc-b z 'vc-c m 'vc-m sv 'vc-s fv 'vc-f T 'vc-T
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        ;; destructure min/max facts
        minp (fn [u v] (let [w (mn u v) f* (call 'signed/min-select-cases u v) R (pconj (le w v) (disj (eqv w u) (eqv w v)))]
                         {:v w :lo-u (fst (le w u) R f*) :lo-v (fst (le w v) (disj (eqv w u) (eqv w v)) (snd (le w u) R f*))
                          :or (snd (le w v) (disj (eqv w u) (eqv w v)) (snd (le w u) R f*))}))
        maxp (fn [u v] (let [w (mx u v) f* (call 'signed/max-select-cases u v) R (pconj (le v w) (disj (eqv w u) (eqv w v)))]
                         {:v w :hi-u (fst (le u w) R f*) :hi-v (fst (le v w) (disj (eqv w u) (eqv w v)) (snd (le u w) R f*))
                          :or (snd (le v w) (disj (eqv w u) (eqv w v)) (snd (le u w) R f*))}))
        P (minp x y) M (maxp x y) Rr (minp (:v M) z) Md (maxp (:v P) (:v Rr))
        p (:v P) Mv (:v M) r (:v Rr) md (:v Md)
        Disj3 (disj (eqv m x) (disj (eqv m y) (eqv m z)))
        d1 (fn [h] (inl (eqv m x) (disj (eqv m y) (eqv m z)) h))
        d2 (fn [h] (inr (eqv m x) (disj (eqv m y) (eqv m z)) (inl (eqv m y) (eqv m z) h)))
        d3 (fn [h] (inr (eqv m x) (disj (eqv m y) (eqv m z)) (inr (eqv m y) (eqv m z) h)))
        which (cases (eqv md p) (eqv md r) Disj3 (:or Md)
                     (f/lam [['vc-mp (eqv md p)]]
                            (let [mp (trans m md p 'vc-hm 'vc-mp)]
                              (cases (eqv p x) (eqv p y) Disj3 (:or P)
                                     (f/lam [['vc-px (eqv p x)]] (d1 (trans m p x mp 'vc-px)))
                                     (f/lam [['vc-py (eqv p y)]] (d2 (trans m p y mp 'vc-py))))))
                     (f/lam [['vc-mr (eqv md r)]]
                            (let [mr (trans m md r 'vc-hm 'vc-mr)]
                              (cases (eqv r Mv) (eqv r z) Disj3 (:or Rr)
                                     (f/lam [['vc-rM (eqv r Mv)]]
                                            (let [mM (trans m r Mv mr 'vc-rM)]
                                              (cases (eqv Mv x) (eqv Mv y) Disj3 (:or M)
                                                     (f/lam [['vc-Mx (eqv Mv x)]] (d1 (trans m Mv x mM 'vc-Mx)))
                                                     (f/lam [['vc-My (eqv Mv y)]] (d2 (trans m Mv y mM 'vc-My))))))
                                     (f/lam [['vc-rz (eqv r z)]] (d3 (trans m r z mr 'vc-rz)))))))
        sm (sym m md 'vc-hm)
        lo (le-resp p p md m (refl p) sm (:hi-u Md))
        hi (cases (eqv md p) (eqv md r) (le m Mv) (:or Md)
                  (f/lam [['vd-mp (eqv md p)]] (le-resp p m Mv Mv (sym m p (trans m md p 'vc-hm 'vd-mp)) (refl Mv) (le-trans p x Mv (:lo-u P) (:hi-u M))))
                  (f/lam [['vd-mr (eqv md r)]] (le-resp r m Mv Mv (sym m r (trans m md r 'vc-hm 'vd-mr)) (refl Mv) (:lo-u Rr))))
        X (maxp y z) X3 (maxp x (:v X)) Y (minp y z) Y3 (minp x (:v Y))
        sp-nn (le-resp s/zero s/zero (sub (:v X3) (:v Y3)) sv (refl s/zero) (sym sv (sub (:v X3) (:v Y3)) 'vc-hs)
                       (diff-nn (:v Y3) (:v X3) (le-trans (:v Y3) x (:v X3) (:lo-u Y3) (:hi-u X3))))
        rd (call 'signed/le-indicator-reading sv T)
        li (nsfr/le-ind sv T)
        A (fn [w] (pconj (le sv T) (eqv w one))) B (fn [w] (pconj (call 'signed/less-than T sv) (eqv w s/zero)))
        rdf (cases (A li) (B li) (nsfr/reading sv T fv) rd
                   (f/lam [['ve-a (A li)]] (inl (A fv) (B fv) (conjoin (le sv T) (eqv fv one) (fst (le sv T) (eqv li one) 've-a)
                                                                        (trans fv li one 'vc-hf (snd (le sv T) (eqv li one) 've-a)))))
                   (f/lam [['ve-b (B li)]] (inr (A fv) (B fv) (conjoin (call 'signed/less-than T sv) (eqv fv s/zero) (fst (call 'signed/less-than T sv) (eqv li s/zero) 've-b)
                                                                        (trans fv li s/zero 'vc-hf (snd (call 'signed/less-than T sv) (eqv li s/zero) 've-b))))))]
    (s/spec 'signed/voter-cell [['vc-a signed] ['vc-b signed] ['vc-c signed] ['vc-m signed] ['vc-s signed] ['vc-f signed] ['vc-T signed]
                                ['vc-hm (eqv m (med x y z))] ['vc-hs (eqv sv (spr x y z))] ['vc-hf (eqv fv (nsfr/le-ind sv T))]]
            (cell-facts x y z m sv fv T)
            (conjoin Disj3 (pconj (le p m) (pconj (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv)))) which
                     (conjoin (le p m) (pconj (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv))) lo
                              (conjoin (le m Mv) (pconj (le s/zero sv) (nsfr/reading sv T fv)) hi
                                       (conjoin (le s/zero sv) (nsfr/reading sv T fv) sp-nn rdf)))))))

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

(def theorem-specs [max-select-spec cell-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-voter-readings [ful/min-select-spec nsfr/reading-spec]) (support/extend-with-shared :expr-sum-voter-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.voter-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
