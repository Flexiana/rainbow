(ns rainbow.math.lemmas.mmck-unique
  "General lemmas: mmck unique. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.multiply-positive :as multiply-positive]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def nnzero (f/const* 'nnrat/zero []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn pneg [p] (call 'proposition/negation p))

(defn explode [p h] (call 'proposition/explode p h))

(defn nat-le [x y] (call 'nat/at-most x y))

(defn assoc3 [x y z] (call 'signed/multiply-associative x y z))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn swap-tail [z m q]
  (a/chain (mul (mul z m) q) [(mul z (mul m q)) (assoc3 z m q)]
           [(mul z (mul q m)) (mcong z z (mul m q) (mul q m) (refl z) (comm m q))]
           [(mul (mul z q) m) (sym (mul (mul z q) m) (mul z (mul q m)) (assoc3 z q m))]))

(defn of-nat [n] (call 'signed/from-nnrat (call 'nnrat/make n s/nz)))

(def cancel-or-zero-spec
  (let [diff (sub 'a 'b)
        product (a/chain (mul diff 'd)
                         [(add (mul 'a 'd) (mul (neg 'b) 'd)) (call 'signed/multiply-distributes-add-right 'a (neg 'b) 'd)]
                         [(add (mul 'a 'd) (neg (mul 'b 'd)))
                          (s/add-cong (mul 'a 'd) (mul 'a 'd) (mul (neg 'b) 'd) (neg (mul 'b 'd)) (refl (mul 'a 'd))
                                      (call 'signed/multiply-negate-left 'b 'd))]
                         [(add (mul 'b 'd) (neg (mul 'b 'd)))
                          (s/add-cong (mul 'a 'd) (mul 'b 'd) (neg (mul 'b 'd)) (neg (mul 'b 'd)) 'h (refl (neg (mul 'b 'd))))]
                         [s/zero (ring (add (mul 'b 'd) (neg (mul 'b 'd))) s/zero)])
        goal (disj (eqv 'a 'b) (eqv 'd s/zero))]
    (s/spec 'signed/multiply-cancel-or-zero [['a signed] ['b signed] ['d signed] ['h (eqv (mul 'a 'd) (mul 'b 'd))]]
            goal
            (cases (eqv diff s/zero) (eqv 'd s/zero) goal (call 'signed/multiply-zero-split diff 'd product)
                   (f/lam [['h1 (eqv diff s/zero)]]
                          (call 'proposition/left-disjunct (eqv 'a 'b) (eqv 'd s/zero)
                                (a/chain 'a [(add diff 'b) (ring 'a (add diff 'b))]
                                         [(add s/zero 'b) (s/add-cong diff s/zero 'b 'b 'h1 (refl 'b))]
                                         ['b (ring (add s/zero 'b) 'b)])))
                   (f/lam [['h2 (eqv 'd s/zero)]] (call 'proposition/right-disjunct (eqv 'a 'b) (eqv 'd s/zero) 'h2))))))

(def cancel-positive-spec
  (s/spec 'signed/multiply-cancel-positive-right
          [['a signed] ['b signed] ['d signed] ['hd (lt s/zero 'd)] ['h (eqv (mul 'a 'd) (mul 'b 'd))]]
          (eqv 'a 'b)
          (cases (eqv 'a 'b) (eqv 'd s/zero) (eqv 'a 'b) (call 'signed/multiply-cancel-or-zero 'a 'b 'd 'h)
                 (f/lam [['same (eqv 'a 'b)]] 'same)
                 (f/lam [['dz (eqv 'd s/zero)]]
                        (explode (eqv 'a 'b)
                                 (f/app (call 'proposition/right (le s/zero 'd) (pneg (eqv s/zero 'd)) 'hd)
                                        (sym 'd s/zero 'dz)))))))

(def successor-positive-spec
  (let [W (call 'nnrat/make (s/succ 'm) s/nz)
        x (of-nat (s/succ 'm))
        nn-trans (fn [p q r h k] (call 'nnrat/equivalent-transitive p q r h k))
        nn-add (fn [p q] (call 'nnrat/add p q))
        X (call 'nat/multiply 'm (s/succ s/nz))]
    (s/spec 'signed/of-nat-successor-positive [['m nat]]
            (lt s/zero x)
            (call 'signed/less-than-intro s/zero x
                  (call 'signed/zero-at-most-of-nonnegative x (call 'nnrat/zero-at-most W))
                  (f/lam [['h0 (eqv s/zero x)]]
                         ;; x ~ 0 unfolds to (W + 0) ~ (0 + 0); W ~ 0 unfolds to succ(m 1) = 0
                         (f/app (call 'nat/zero-not-successor X)
                                (f/app (f/const* 'equality/symmetric [type-level]) nat (s/succ X) s/nz
                                       (nn-trans W (nn-add W nnzero) nnzero
                                                 (call 'nnrat/equivalent-symmetric (nn-add W nnzero) W (call 'nnrat/add-zero-right W))
                                                 (nn-trans (nn-add W nnzero) (nn-add nnzero nnzero) nnzero
                                                           (sym s/zero x 'h0) (call 'nnrat/add-zero-right nnzero))))))))))

(defn balance [p l d K] (s/all-below K (fn [k] (eqv (mul (at p k) l) (mul (at p (s/succ k)) (at d k))))))

(defn recursion-binders [p q d e l m K]
  [['hd (s/all-below K #(lt s/zero (at d %)))]
   ['hp (balance p l d K)] ['hq (balance q m e K)]
   ['hl (eqv l m)] ['he (s/all-below K #(eqv (at e %) (at d %)))]])

(def base-binders [['p family] ['q family] ['d family] ['e family] ['l signed] ['m signed] ['K nat]])

(defn induct [claim base step n]
  (f/app (f/const* 'data/Nat.rec [prop-level])
         (f/lam [['rec-k nat]] (claim 'rec-k)) base
         (f/lam [['rec-j nat] ['rec-ih (claim 'rec-j)]] (step 'rec-j 'rec-ih)) n))

(defn lower [j K h]                                    ; succ j <= K  ->  j <= K
  (call 'nat/at-most-transitive j (s/succ j) K (call 'nat/at-most-successor j) h))

(def proportional-spec
  (let [claim (fn [k] (f/forall [['hk (nat-le k 'K)]] (eqv (mul (at 'p k) (at 'q s/nz)) (mul (at 'q k) (at 'p s/nz)))))
        p0 (at 'p s/nz) q0 (at 'q s/nz)]
    (s/spec 'signed/birth-death-proportional
            (-> base-binders (into (recursion-binders 'p 'q 'd 'e 'l 'm 'K)) (conj ['k nat]))
            (claim 'k)
            (induct claim
                      (f/lam [['hk0 (nat-le s/nz 'K)]] (comm p0 q0))
                      (fn [j ih]
                        (let [h1 'hk1
                              pj (at 'p j) p1 (at 'p (s/succ j)) qj (at 'q j) q1 (at 'q (s/succ j)) dj (at 'd j) ej (at 'e j)
                              IH (at ih (lower j 'K h1))
                              cross (a/chain (mul (mul p1 q0) dj)
                                             [(mul (mul p1 dj) q0) (swap-tail p1 q0 dj)]
                                             [(mul (mul pj 'l) q0) (mcong (mul p1 dj) (mul pj 'l) q0 q0 (sym (mul pj 'l) (mul p1 dj) (at 'hp j h1)) (refl q0))]
                                             [(mul (mul pj q0) 'l) (swap-tail pj 'l q0)]
                                             [(mul (mul qj p0) 'l) (mcong (mul pj q0) (mul qj p0) 'l 'l IH (refl 'l))]
                                             [(mul (mul qj 'l) p0) (swap-tail qj p0 'l)]
                                             [(mul (mul qj 'm) p0) (mcong (mul qj 'l) (mul qj 'm) p0 p0 (mcong qj qj 'l 'm (refl qj) 'hl) (refl p0))]
                                             [(mul (mul q1 ej) p0) (mcong (mul qj 'm) (mul q1 ej) p0 p0 (at 'hq j h1) (refl p0))]
                                             [(mul (mul q1 dj) p0) (mcong (mul q1 ej) (mul q1 dj) p0 p0 (mcong q1 q1 ej dj (refl q1) (at 'he j h1)) (refl p0))]
                                             [(mul (mul q1 p0) dj) (swap-tail q1 dj p0)])]
                          (f/lam [[h1 (nat-le (s/succ j) 'K)]]
                                 (call 'signed/multiply-cancel-positive-right (mul p1 q0) (mul q1 p0) dj (at 'hd j h1) cross))))
                      'k))))

(def zero-propagates-spec
  (let [claim (fn [k] (f/forall [['hk (nat-le k 'K)]] (eqv (at 'p k) s/zero)))]
    (s/spec 'signed/birth-death-zero-propagates
            [['p family] ['d family] ['l signed] ['K nat]
             ['hd (s/all-below 'K #(lt s/zero (at 'd %)))] ['hp (balance 'p 'l 'd 'K)] ['h0 (eqv (at 'p s/nz) s/zero)] ['k nat]]
            (claim 'k)
            (induct claim
                      (f/lam [['hk0 (nat-le s/nz 'K)]] 'h0)
                      (fn [j ih]
                        (let [h1 'hz1 pj (at 'p j) p1 (at 'p (s/succ j)) dj (at 'd j)
                              down (a/chain (mul p1 dj)
                                            [(mul pj 'l) (sym (mul pj 'l) (mul p1 dj) (at 'hp j h1))]
                                            [(mul s/zero 'l) (mcong pj s/zero 'l 'l (at ih (lower j 'K h1)) (refl 'l))]
                                            [s/zero (call 'signed/multiply-zero-left 'l)]
                                            [(mul s/zero dj) (sym (mul s/zero dj) s/zero (call 'signed/multiply-zero-left dj))])]
                          (f/lam [[h1 (nat-le (s/succ j) 'K)]]
                                 (call 'signed/multiply-cancel-positive-right p1 s/zero dj (at 'hd j h1) down))))
                      'k))))

(defn total [p K] (sum (f/lam [['tk nat]] (at p 'tk)) (s/succ K)))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [cancel-or-zero-spec cancel-positive-spec successor-positive-spec proportional-spec zero-propagates-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.rational.signed.multiply-positive rainbow.math.rational.signed.multiply-associative rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-mmck-unique theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.mmck-unique))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
