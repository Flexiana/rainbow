(ns rainbow.math.lemmas.sir-readings
  "General lemmas: sir readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.ncyc-infeasible :as ncyc]
            [rainbow.math.lemmas.chisq-readings :as chisq]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
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

(defn inf [b S I] (mul b (mul S I)))

(defn rec [g I] (mul g I))

(defn step-hyps [S I R S1 I1 R1 b g]
  [['sh-s (eqv S1 (add S (neg (inf b S I))))]
   ['sh-i (eqv I1 (add I (add (inf b S I) (neg (rec g I)))))]
   ['sh-r (eqv R1 (add R (rec g I)))]])

(defn pop [S I R] (add S (add I R)))

(defn ident-claim [S I R S1 I1 R1 b g]
  (pconj (eqv (pop S1 I1 R1) (pop S I R)) (eqv (sub I1 I) (mul I (add (mul b S) (neg g))))))

(defn nn3 [S I R] (pconj (le s/zero S) (pconj (le s/zero I) (le s/zero R))))

(defn inf-as [b S I which]
  (case which
    :i (chain [(inf b S I) (mul (mul b S) I) (mul I (mul b S))]
              [(sym (mul (mul b S) I) (inf b S I) (call 'signed/multiply-associative b S I))
               (call 'signed/multiply-commutative (mul b S) I)])
    :s (chain [(inf b S I) (mul (mul b S) I) (mul (mul S b) I) (mul S (mul b I))]
              [(sym (mul (mul b S) I) (inf b S I) (call 'signed/multiply-associative b S I))
               (mcong (mul b S) (mul S b) I I (call 'signed/multiply-commutative b S) (refl I))
               (call 'signed/multiply-associative S b I)])))

(defn times-one-minus [x y]
  (chain [(mul x (add one (neg y))) (add (mul x one) (mul x (neg y))) (add x (neg (mul x y)))]
         [(dl x one (neg y))
          (acong (mul x one) x (mul x (neg y)) (neg (mul x y))
                 (trans (mul x one) (mul one x) x (call 'signed/multiply-commutative x one) (call 'signed/multiply-one-left x))
                 (mul-neg x y))]))

(def ident-spec
  (let [[S I R S1 I1 R1 b g] '[si-s si-i si-r si-s1 si-i1 si-r1 si-b si-g]
        B (inf b S I) G (rec g I)
        p1 (acong S1 (add S (neg B)) (add I1 R1) (add (add I (add B (neg G))) (add R G)) 'sh-s
                  (acong I1 (add I (add B (neg G))) R1 (add R G) 'sh-i 'sh-r))
        cons (trans (pop S1 I1 R1) (add (add S (neg B)) (add (add I (add B (neg G))) (add R G))) (pop S I R) p1
                    (ring-atoms [['sa-s S] ['sa-i I] ['sa-r R] ['sa-b B] ['sa-g G]]
                                (add (add 'sa-s (neg 'sa-b)) (add (add 'sa-i (add 'sa-b (neg 'sa-g))) (add 'sa-r 'sa-g)))
                                (add 'sa-s (add 'sa-i 'sa-r))))
        IbS (mul I (mul b S)) Ig (mul I g)
        grow (chain [(sub I1 I) (sub (add I (add B (neg G))) I) (add B (neg G)) (add IbS (neg Ig)) (add IbS (mul I (neg g))) (mul I (add (mul b S) (neg g)))]
                    [(acong I1 (add I (add B (neg G))) (neg I) (neg I) 'sh-i (refl (neg I)))
                     (ring-atoms [['sg-i I] ['sg-b B] ['sg-g G]] (sub (add 'sg-i (add 'sg-b (neg 'sg-g))) 'sg-i) (add 'sg-b (neg 'sg-g)))
                     (acong B IbS (neg G) (neg Ig) (inf-as b S I :i) (negc G Ig (call 'signed/multiply-commutative g I)))
                     (acong IbS IbS (neg Ig) (mul I (neg g)) (refl IbS) (sym (mul I (neg g)) (neg Ig) (mul-neg I g)))
                     (sym (mul I (add (mul b S) (neg g))) (add IbS (mul I (neg g))) (dl I (mul b S) (neg g)))])]
    (s/spec 'signed/sir-step-identities
            (into [[S signed] [I signed] [R signed] [S1 signed] [I1 signed] [R1 signed] [b signed] [g signed]] (step-hyps S I R S1 I1 R1 b g))
            (ident-claim S I R S1 I1 R1 b g)
            (conjoin (eqv (pop S1 I1 R1) (pop S I R)) (eqv (sub I1 I) (mul I (add (mul b S) (neg g)))) cons grow))))

(def nonneg-spec
  (let [[S I R S1 I1 R1 b g] '[sn-s sn-i sn-r sn-s1 sn-i1 sn-r1 sn-b sn-g]
        B (inf b S I) G (rec g I) bI (mul b I)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        hn 'sn-hn hS (fst (le s/zero S) (pconj (le s/zero I) (le s/zero R)) hn)
        hI (fst (le s/zero I) (le s/zero R) (snd (le s/zero S) (pconj (le s/zero I) (le s/zero R)) hn))
        hR (snd (le s/zero I) (le s/zero R) (snd (le s/zero S) (pconj (le s/zero I) (le s/zero R)) hn))
        one-minus-nn (fn [y hy] (le-resp (add y (neg y)) s/zero (add one (neg y)) (add one (neg y))
                                          (ring-atoms [['so-y y]] (add 'so-y (neg 'so-y)) s/zero) (refl (add one (neg y)))
                                          (call 'signed/add-right-monotone y one (neg y) hy)))
        ;; S1 ~ S (1 - b I) >= 0
        S1eq (chain [(mul S (add one (neg bI))) (add S (neg (mul S bI))) (add S (neg B)) S1]
                    [(times-one-minus S bI)
                     (acong S S (neg (mul S bI)) (neg B) (refl S) (negc (mul S bI) B (sym B (mul S bI) (inf-as b S I :s))))
                     (sym S1 (add S (neg B)) 'sh-s)])
        s1nn (le-resp s/zero s/zero (mul S (add one (neg bI))) S1 (refl s/zero) S1eq (nn-prod S (add one (neg bI)) hS (one-minus-nn bI 'sn-hbi)))
        ;; I1 ~ I (1 - g) + b (S I) >= 0
        iq (mul I (add one (neg g)))
        I1eq (chain [(add iq B) (add (add I (neg (mul I g))) B) (add (add I (neg G)) B) (add I (add B (neg G))) I1]
                    [(acong iq (add I (neg (mul I g))) B B (times-one-minus I g) (refl B))
                     (acong (add I (neg (mul I g))) (add I (neg G)) B B
                            (acong I I (neg (mul I g)) (neg G) (refl I) (negc (mul I g) G (call 'signed/multiply-commutative I g))) (refl B))
                     (ring-atoms [['sj-i I] ['sj-g G] ['sj-b B]] (add (add 'sj-i (neg 'sj-g)) 'sj-b) (add 'sj-i (add 'sj-b (neg 'sj-g))))
                     (sym I1 (add I (add B (neg G))) 'sh-i)])
        sum-nn (fn [x y hx hy] (le-resp (add s/zero s/zero) s/zero (add x y) (add x y) (ring (add s/zero s/zero) s/zero) (refl (add x y))
                                        (call 'signed/add-monotone s/zero x s/zero y hx hy)))
        i1nn (le-resp s/zero s/zero (add iq B) I1 (refl s/zero) I1eq
                      (sum-nn iq B (nn-prod I (add one (neg g)) hI (one-minus-nn g 'sn-hg1))
                              (nn-prod b (mul S I) 'sn-hb (nn-prod S I hS hI))))
        r1nn (le-resp s/zero s/zero (add R G) R1 (refl s/zero) (sym R1 (add R G) 'sh-r)
                      (sum-nn R G hR (nn-prod g I 'sn-hg hI)))]
    (s/spec 'signed/sir-step-nonnegative
            (into [[S signed] [I signed] [R signed] [S1 signed] [I1 signed] [R1 signed] [b signed] [g signed]]
                  (concat (step-hyps S I R S1 I1 R1 b g)
                          [['sn-hb (le s/zero b)] ['sn-hg (le s/zero g)] ['sn-hg1 (le g one)] ['sn-hbi (le bI one)] ['sn-hn (nn3 S I R)]]))
            (nn3 S1 I1 R1)
            (conjoin (le s/zero S1) (pconj (le s/zero I1) (le s/zero R1)) s1nn (conjoin (le s/zero I1) (le s/zero R1) i1nn r1nn)))))

(defn popf [Sf If Rf] (f/lam [['tq nat]] (pop (at Sf 'tq) (at If 'tq) (at Rf 'tq))))

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

(def borrowed-specs [ncyc/telescope-spec chisq/eq-of-diff-spec])

(def theorem-specs [ident-spec nonneg-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-sir-readings borrowed-specs) (support/extend-with-shared :expr-sum-sir-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.sir-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
