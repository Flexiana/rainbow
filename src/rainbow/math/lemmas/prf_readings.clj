(ns rainbow.math.lemmas.prf-readings
  "General lemmas: prf readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.lemmas.ncyc-infeasible :as pdep6]
            [rainbow.math.lemmas.cpm-makespan :as pdep5]
            [rainbow.math.lemmas.indep-set-dual :as pdep3]
            [rainbow.math.rational.signed.lp-duality-on :as pdep2]
            [rainbow.math.lemmas.kmeans-nearest :as pdep1]
            [rainbow.math.lemmas.pcmax-lower-bound :as pdep0]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
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
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.strict-order :as strict]
            [rainbow.math.checks :as combinators]
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

(defn lt [x y] (call 'signed/less-than x y))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(def positive-spec
  (let [x 'po-x]
    (s/spec 'signed/positive-of-at-least-one [[x signed] ['po-h (le one x)]]
            (lt s/zero x)
            (call 'signed/less-than-intro s/zero x (call 'signed/at-most-transitive s/zero one x zero-le-one 'po-h)
                  (f/lam [['po-e (eqv s/zero x)]]
                         (call 'signed/one-not-at-most-zero (le-resp one one x s/zero (refl one) (sym s/zero x 'po-e) 'po-h)))))))

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(def two-eq
  (let [o1 (of-nat/of-nat (s/succ s/nz)) o0 (of-nat/of-nat s/nz)
        o1-one (chain [o1 (add o0 one) (add s/zero one) one]
                      [(call 'signed/of-nat-successor s/nz)
                       (acong o0 s/zero one one (refl s/zero) (refl one))
                       (ring (add s/zero one) one)])]
    (chain [two (add o1 one) (add one one)]
           [(call 'signed/of-nat-successor (s/succ s/nz)) (acong o1 one one one o1-one (refl one))])))

(defn twice [T] (chain [(mul two T) (mul (add one one) T) (add (mul one T) (mul one T)) (add T T)]
                        [(mcong two (add one one) T T two-eq (refl T)) (dr one one T)
                         (acong (mul one T) T (mul one T) T (call 'signed/multiply-one-left T) (call 'signed/multiply-one-left T))]))

(def f1-spec
  (let [[T FP FN P R F] '[fh-t fh-fp fh-fn fh-p fh-r fh-f]
        a (add T FP) b (add T FN) TT (mul T T) PR (mul P R)
        den (add (mul two T) (add FP FN))
        hden (chain [den (add (add T T) (add FP FN)) (add a b)]
                    [(acong (mul two T) (add T T) (add FP FN) (add FP FN) (twice T) (refl (add FP FN)))
                     (ring-atoms [['fd-t T] ['fd-p FP] ['fd-n FN]] (add (add 'fd-t 'fd-t) (add 'fd-p 'fd-n)) (add (add 'fd-t 'fd-p) (add 'fd-t 'fd-n)))])
        hF2 (chain [(mul F (add a b)) (mul F den) (mul two T) (add T T)]
                   [(mcong F F (add a b) den (refl F) (sym den (add a b) hden)) 'fh-hf (twice T)])
        ;; P (a b) ~ T b and R (a b) ~ T a
        Pab (chain [(mul P (mul a b)) (mul (mul P a) b) (mul T b)]
                   [(sym (mul (mul P a) b) (mul P (mul a b)) (call 'signed/multiply-associative P a b))
                    (mcong (mul P a) T b b 'fh-hp (refl b))])
        Rab (chain [(mul R (mul a b)) (mul R (mul b a)) (mul (mul R b) a) (mul T a)]
                   [(mcong R R (mul a b) (mul b a) (refl R) (call 'signed/multiply-commutative a b))
                    (sym (mul (mul R b) a) (mul R (mul b a)) (call 'signed/multiply-associative R b a))
                    (mcong (mul R b) T a a 'fh-hr (refl a))])
        X (mul F (add P R)) Y (add PR PR) ab (mul a b)
        ;; X ab ~ (T + T) T
        Tba (add (mul T b) (mul T a))
        hX (chain [(mul X ab) (mul F (mul (add P R) ab)) (mul F (add (mul P ab) (mul R ab))) (mul F Tba)
                   (mul F (mul (add a b) T)) (mul (mul F (add a b)) T) (mul (add T T) T)]
                  [(call 'signed/multiply-associative F (add P R) ab)
                   (mcong F F (mul (add P R) ab) (add (mul P ab) (mul R ab)) (refl F) (dr P R ab))
                   (mcong F F (add (mul P ab) (mul R ab)) Tba (refl F) (acong (mul P ab) (mul T b) (mul R ab) (mul T a) Pab Rab))
                   (mcong F F Tba (mul (add a b) T) (refl F)
                          (chain [Tba (add (mul T a) (mul T b)) (mul T (add a b)) (mul (add a b) T)]
                                 [(ring-atoms [['fb-x (mul T b)] ['fb-y (mul T a)]] (add 'fb-x 'fb-y) (add 'fb-y 'fb-x))
                                  (sym (mul T (add a b)) (add (mul T a) (mul T b)) (dl T a b))
                                  (call 'signed/multiply-commutative T (add a b))]))
                   (sym (mul (mul F (add a b)) T) (mul F (mul (add a b) T)) (call 'signed/multiply-associative F (add a b) T))
                   (mcong (mul F (add a b)) (add T T) T T hF2 (refl T))])
        ;; PR ab ~ T T
        hPR (chain [(mul PR ab) (mul P (mul R ab)) (mul P (mul T a)) (mul P (mul a T)) (mul (mul P a) T) TT]
                   [(call 'signed/multiply-associative P R ab)
                    (mcong P P (mul R ab) (mul T a) (refl P) Rab)
                    (mcong P P (mul T a) (mul a T) (refl P) (call 'signed/multiply-commutative T a))
                    (sym (mul (mul P a) T) (mul P (mul a T)) (call 'signed/multiply-associative P a T))
                    (mcong (mul P a) T T T 'fh-hp (refl T))])
        hY (chain [(mul Y ab) (add (mul PR ab) (mul PR ab)) (add TT TT)]
                  [(dr PR PR ab) (acong (mul PR ab) TT (mul PR ab) TT hPR hPR)])
        hXY (chain [(mul X ab) (mul (add T T) T) (add TT TT) (mul Y ab)]
                   [hX (dr T T T) (sym (mul Y ab) (add TT TT) hY)])
        pa (call 'signed/positive-of-at-least-one a 'fh-ha) pb (call 'signed/positive-of-at-least-one b 'fh-hb)
        ;; X (a b) ~ Y (a b)  ->  (X a) b ~ (Y a) b  ->  X a ~ Y a  ->  X ~ Y
        hXa (call 'signed/multiply-cancel-positive-right (mul X a) (mul Y a) b pb
                  (chain [(mul (mul X a) b) (mul X ab) (mul Y ab) (mul (mul Y a) b)]
                         [(call 'signed/multiply-associative X a b) hXY
                          (sym (mul (mul Y a) b) (mul Y ab) (call 'signed/multiply-associative Y a b))]))]
    (s/spec 'signed/f1-harmonic
            [[T signed] [FP signed] [FN signed] [P signed] [R signed] [F signed]
             ['fh-hp (eqv (mul P a) T)] ['fh-hr (eqv (mul R b) T)] ['fh-hf (eqv (mul F den) (mul two T))]
             ['fh-ha (le one a)] ['fh-hb (le one b)]]
            (eqv X Y)
            (call 'signed/multiply-cancel-positive-right X Y a pa hXa))))

(def split-spec
  (let [[y h] '[sp-y sp-h] yh (mul y h)
        c1 (chain [(add yh (mul (add one (neg y)) h)) (add yh (add (mul one h) (mul (neg y) h))) (add yh (add h (neg yh))) h]
                  [(acong yh yh (mul (add one (neg y)) h) (add (mul one h) (mul (neg y) h)) (refl yh) (dr one (neg y) h))
                   (acong yh yh (add (mul one h) (mul (neg y) h)) (add h (neg yh)) (refl yh)
                          (acong (mul one h) h (mul (neg y) h) (neg yh) (call 'signed/multiply-one-left h) (neg-mul y h)))
                   (ring-atoms [['sq-a yh] ['sq-h h]] (add 'sq-a (add 'sq-h (neg 'sq-a))) 'sq-h)])
        yone (trans (mul y one) (mul one y) y (call 'signed/multiply-commutative y one) (call 'signed/multiply-one-left y))
        c2 (chain [(add yh (mul y (add one (neg h)))) (add yh (add (mul y one) (mul y (neg h)))) (add yh (add y (neg yh))) y]
                  [(acong yh yh (mul y (add one (neg h))) (add (mul y one) (mul y (neg h))) (refl yh) (dl y one (neg h)))
                   (acong yh yh (add (mul y one) (mul y (neg h))) (add y (neg yh)) (refl yh)
                          (acong (mul y one) y (mul y (neg h)) (neg yh) yone (mul-neg y h)))
                   (ring-atoms [['sr-a yh] ['sr-y y]] (add 'sr-a (add 'sr-y (neg 'sr-a))) 'sr-y)])]
    (s/spec 'signed/indicator-cell-split [[y signed] [h signed]]
            (pconj (eqv (add yh (mul (add one (neg y)) h)) h) (eqv (add yh (mul y (add one (neg h)))) y))
            (conjoin (eqv (add yh (mul (add one (neg y)) h)) h) (eqv (add yh (mul y (add one (neg h)))) y) c1 c2))))

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

(def borrowed-specs [mmck/cancel-or-zero-spec mmck/cancel-positive-spec])

(def theorem-specs [positive-spec f1-spec split-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.pcmax-lower-bound rainbow.math.lemmas.kmeans-nearest rainbow.math.rational.signed.lp-duality-on rainbow.math.lemmas.indep-set-dual rainbow.math.lemmas.mmck-unique rainbow.math.lemmas.cpm-makespan rainbow.math.lemmas.ncyc-infeasible rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-prf-readings borrowed-specs) (support/extend-with-shared :expr-sum-prf-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.prf-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
