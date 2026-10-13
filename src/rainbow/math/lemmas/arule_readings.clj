(ns rainbow.math.lemmas.arule-readings
  "General lemmas: arule readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.auc-readings :as auc]
            [rainbow.math.lemmas.payasbid-readings :as pab]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.lemmas.prf-readings :as prf]
            [rainbow.math.lemmas.chisq-readings :as chisq]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.deviation-rows :as deviation]
            [rainbow.math.rational.signed.strict-order :as strict]
            [rainbow.math.checks :as combinators]))

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

(defn comp [x] (add one (neg x)))

(defn r1 [pairs x y] (ring-atoms pairs x y))

(defn one-minus-le [x y h] (call 'signed/add-left-monotone (neg y) (neg x) one (call 'signed/negate-reverses-order x y h)))

(defn le-one-of-comp [x h]
  (le-resp (add s/zero x) x (add (comp x) x) one (r1 [['lo-x x]] (add s/zero 'lo-x) 'lo-x)
           (r1 [['lo-o one] ['lo-y x]] (add (add 'lo-o (neg 'lo-y)) 'lo-y) 'lo-o)
           (call 'signed/add-right-monotone s/zero (comp x) x h)))

(defn comp-le-one [x h]
  (le-resp (comp x) (comp x) (add one (neg s/zero)) one (refl (comp x)) (r1 [['lc-o one]] (add 'lc-o (neg s/zero)) 'lc-o)
           (one-minus-le s/zero x h)))

(defn comp-nn [x h]
  (le-resp (add x (neg x)) s/zero (add one (neg x)) (comp x) (r1 [['ln-x x]] (add 'ln-x (neg 'ln-x)) s/zero) (refl (comp x))
           (call 'signed/add-right-monotone x one (neg x) h)))

(defn union [a b] (add a (add b (neg (mul a b)))))

(defn factor [m T] (comp (mul m (comp T))))

(defn factor-claim [a b T] (let [fA (factor a T) fU (factor (union a b) T)] (pconj (le s/zero fU) (pconj (le fU fA) (le fA one)))))

(def factor-spec
  (let [[a b T] '[af-a af-b af-t] D (comp T) u (union a b) xA (mul a D) xU (mul u D)
        z01 (fn [x] (eqv (mul x (sub one x)) s/zero))
        ha0 (call 'signed/zero-one-nonnegative a 'af-ha) hac (call 'signed/complement-nonnegative a 'af-ha) ha1 (le-one-of-comp a hac)
        hb0 (call 'signed/zero-one-nonnegative b 'af-hb) hbc (call 'signed/complement-nonnegative b 'af-hb) hb1 (le-one-of-comp b hbc)
        hT0 (call 'signed/zero-one-nonnegative T 'af-ht)
        hD0 (call 'signed/complement-nonnegative T 'af-ht) hD1 (comp-le-one T hT0)
        oneD (call 'signed/multiply-one-left D)
        ;; u ~ a + b (1 - a), so a <= u
        bca (mul b (comp a))
        hbca (chain [bca (add (mul b one) (mul b (neg a))) (add b (neg (mul b a))) (add b (neg (mul a b)))]
                    [(dl b one (neg a))
                     (acong (mul b one) b (mul b (neg a)) (neg (mul b a))
                            (trans (mul b one) (mul one b) b (call 'signed/multiply-commutative b one) (call 'signed/multiply-one-left b)) (mul-neg b a))
                     (acong b b (neg (mul b a)) (neg (mul a b)) (refl b) (negc (mul b a) (mul a b) (call 'signed/multiply-commutative b a)))])
        hau (le-resp (add a s/zero) a (add a bca) u (r1 [['lu-a a]] (add 'lu-a s/zero) 'lu-a) (acong a a bca (add b (neg (mul a b))) (refl a) hbca)
                     (call 'signed/add-left-monotone s/zero bca a (nn-prod b (comp a) hb0 hac)))
        ;; u <= 1, by a ~ 0 or 1 - a ~ 0
        hu1 (cases (eqv a s/zero) (eqv (sub one a) s/zero) (le u one) (call 'signed/multiply-zero-split a (sub one a) 'af-ha)
                   (f/lam [['af-a0 (eqv a s/zero)]]
                          (le-resp b u one one
                                   (chain [b (add s/zero (add b (neg (mul s/zero b)))) u]
                                          [(r1 [['lv-b b]] 'lv-b (add s/zero (add 'lv-b (neg (mul s/zero 'lv-b)))))
                                           (sym u (add s/zero (add b (neg (mul s/zero b))))
                                                (acong a s/zero (add b (neg (mul a b))) (add b (neg (mul s/zero b))) 'af-a0
                                                       (acong b b (neg (mul a b)) (neg (mul s/zero b)) (refl b) (negc (mul a b) (mul s/zero b) (mcong a s/zero b b 'af-a0 (refl b))))))])
                                   (refl one) hb1))
                   (f/lam [['af-a1 (eqv (sub one a) s/zero)]]
                          (let [e (call 'signed/eq-of-difference-zero a one 'af-a1)]
                            (le-resp one u one one
                                     (sym u one (chain [u (add one (add b (neg (mul one b)))) (add one (add b (neg b))) one]
                                                       [(acong a one (add b (neg (mul a b))) (add b (neg (mul one b))) e
                                                               (acong b b (neg (mul a b)) (neg (mul one b)) (refl b) (negc (mul a b) (mul one b) (mcong a one b b e (refl b)))))
                                                        (acong one one (add b (neg (mul one b))) (add b (neg b)) (refl one)
                                                               (acong b b (neg (mul one b)) (neg b) (refl b) (negc (mul one b) b (call 'signed/multiply-one-left b))))
                                                        (r1 [['lw-o one] ['lw-b b]] (add 'lw-o (add 'lw-b (neg 'lw-b))) 'lw-o)]))
                                     (refl one) (call 'signed/at-most-reflexive one)))))
        hxA0 (nn-prod a D ha0 hD0)
        hxAU (call 'signed/scaled-term-at-most D a u hD0 hau)
        hxU1 (call 'signed/at-most-transitive xU D one (le-resp xU xU (mul one D) D (refl xU) oneD (call 'signed/scaled-term-at-most D u one hD0 hu1)) hD1)]
    (s/spec 'signed/arule-factor [[a signed] [b signed] [T signed] ['af-ha (z01 a)] ['af-hb (z01 b)] ['af-ht (z01 T)]]
            (factor-claim a b T)
            (conjoin (le s/zero (factor u T)) (pconj (le (factor u T) (factor a T)) (le (factor a T) one)) (comp-nn xU hxU1)
                     (conjoin (le (factor u T) (factor a T)) (le (factor a T) one) (one-minus-le xA xU hxAU) (comp-le-one xA hxA0))))))

(defn prod [G k] (call 'signed/expr-prod-value G k))

(defn unit-claim [G k] (f/forall [['pu-h0 (s/all-below k #(le s/zero (at G %)))] ['pu-h1 (s/all-below k #(le (at G %) one))]]
                                 (pconj (le s/zero (prod G k)) (le (prod G k) one))))

(defn restrict [h q] (f/lam [['rs-i nat] ['rs-b (below 'rs-i q)]] (at h 'rs-i (s/weaken 'rs-i q 'rs-b))))

(def unit-spec
  (let [G 'pu-g]
    (s/spec 'signed/expr-prod-unit-interval [[G family] ['pu-k nat]]
            (unit-claim G 'pu-k)
            (s/induct (fn [k] (unit-claim G k))
                      (f/lam [['pu-h0 (s/all-below s/nz #(le s/zero (at G %)))] ['pu-h1 (s/all-below s/nz #(le (at G %) one))]]
                             (conjoin (le s/zero one) (le one one) zero-le-one (call 'signed/at-most-reflexive one)))
                      (fn [q ih]
                        (let [k (s/succ q) P (prod G q) g (at G q)]
                          (f/lam [['pu-h0 (s/all-below k #(le s/zero (at G %)))] ['pu-h1 (s/all-below k #(le (at G %) one))]]
                                 (let [r (at ih (restrict 'pu-h0 q) (restrict 'pu-h1 q))
                                       P0 (call 'proposition/left (le s/zero P) (le P one) r) P1 (call 'proposition/right (le s/zero P) (le P one) r)
                                       g0 (at 'pu-h0 q (s/self-below q)) g1 (at 'pu-h1 q (s/self-below q))]
                                   (conjoin (le s/zero (mul P g)) (le (mul P g) one) (nn-prod P g P0 g0)
                                            (call 'signed/at-most-transitive (mul P g) g one
                                                  (le-resp (mul P g) (mul P g) (mul one g) g (refl (mul P g)) (call 'signed/multiply-one-left g)
                                                           (call 'signed/scaled-term-at-most g P one g0 P1))
                                                  g1))))))
                      'pu-k))))

(defn mono-claim [F G k] (f/forall [['pm-h0 (s/all-below k #(le s/zero (at F %)))] ['pm-hl (s/all-below k #(le (at F %) (at G %)))]
                                     ['pm-h1 (s/all-below k #(le (at G %) one))]]
                                    (le (prod F k) (prod G k))))

(def mono-spec
  (let [F 'pm-f G 'pm-g]
    (s/spec 'signed/expr-prod-monotone [[F family] [G family] ['pm-k nat]]
            (mono-claim F G 'pm-k)
            (s/induct (fn [k] (mono-claim F G k))
                      (f/lam [['pm-h0 (s/all-below s/nz #(le s/zero (at F %)))] ['pm-hl (s/all-below s/nz #(le (at F %) (at G %)))]
                              ['pm-h1 (s/all-below s/nz #(le (at G %) one))]]
                             (call 'signed/at-most-reflexive one))
                      (fn [q ih]
                        (let [k (s/succ q) PF (prod F q) PG (prod G q) fq (at F q) gq (at G q)]
                          (f/lam [['pm-h0 (s/all-below k #(le s/zero (at F %)))] ['pm-hl (s/all-below k #(le (at F %) (at G %)))]
                                  ['pm-h1 (s/all-below k #(le (at G %) one))]]
                                 (let [h0 (restrict 'pm-h0 q) hl (restrict 'pm-hl q) h1 (restrict 'pm-h1 q)
                                       g0 (f/lam [['pg-i nat] ['pg-b (below 'pg-i q)]]
                                                 (call 'signed/at-most-transitive s/zero (at F 'pg-i) (at G 'pg-i) (at h0 'pg-i 'pg-b) (at hl 'pg-i 'pg-b)))
                                       ug (call 'signed/expr-prod-unit-interval G q g0 h1)
                                       PG0 (call 'proposition/left (le s/zero PG) (le PG one) ug)
                                       f0 (at 'pm-h0 q (s/self-below q)) fg (at 'pm-hl q (s/self-below q))]
                                   (call 'signed/at-most-transitive (mul PF fq) (mul PG fq) (mul PG gq)
                                         (call 'signed/scaled-term-at-most fq PF PG f0 (at ih h0 hl h1))
                                         (call 'signed/multiply-left-monotone PG fq gq PG0 fg))))))
                      'pm-k))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec auc/complement-spec pab/scaled-term-spec mmck/cancel-positive-spec mmck/successor-positive-spec
                     pcmax/cancel-order-spec prf/positive-spec chisq/eq-of-diff-spec rectangular-index/rectangular-spec])

(def theorem-specs [factor-spec unit-spec mono-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      distributive/extend-environment
      unit-laws/extend-environment
      equivalence/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      deviation/extend-environment
      of-nat/extend-environment
      strict/extend-environment
      combinators/extend-environment
      (support/extend-with-shared :expr-sum-arule-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
