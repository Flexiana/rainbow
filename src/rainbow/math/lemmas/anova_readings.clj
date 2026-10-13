(ns rainbow.math.lemmas.anova-readings
  "General lemmas: anova readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]))

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

(defn sqr [x] (mul x x))

(defn ofn [k] (of-nat/of-nat k))

(defn dev [x c] (add x (neg c)))

(defn devsq-fam [F c] (f/lam [['dq-i nat]] (sqr (dev (at F 'dq-i) c))))

(def shift-spec
  (let [[F q m c] '[sh-f sh-q sh-m sh-c] k (s/succ q) N (ofn k)
        b (dev m c) bb (sqr b)
        A (f/lam [['sa-i nat]] (dev (at F 'sa-i) m))
        AA (devsq-fam F m)
        AB (f/lam [['sb-i nat]] (mul (at A 'sb-i) b))
        ABAB (f/lam [['sd-i nat]] (add (at AB 'sd-i) (at AB 'sd-i)))
        BB (f/lam [['se-i nat]] bb)
        Q (f/lam [['sq-i nat]] (add (at ABAB 'sq-i) bb))
        AQ (f/lam [['sr-i nat]] (add (at AA 'sr-i) (at Q 'sr-i)))
        term (f/lam [['st-i nat] ['st-h (below 'st-i k)]]
                    (let [x (at F 'st-i) a (dev x m) ab (mul a b) aa (sqr a)]
                      (chain [(sqr (dev x c)) (sqr (add a b)) (add (mul a (add a b)) (mul b (add a b)))
                              (add (add aa ab) (add (mul b a) bb)) (add (add aa ab) (add ab bb)) (add aa (add (add ab ab) bb))]
                             [(let [h (ring-atoms [['su-x x] ['su-m m] ['su-c c]] (dev 'su-x 'su-c) (add (dev 'su-x 'su-m) (dev 'su-m 'su-c)))]
                                (mcong (dev x c) (add a b) (dev x c) (add a b) h h))
                              (dr a b (add a b))
                              (acong (mul a (add a b)) (add aa ab) (mul b (add a b)) (add (mul b a) bb) (dl a a b) (dl b a b))
                              (acong (add aa ab) (add aa ab) (add (mul b a) bb) (add ab bb) (refl (add aa ab))
                                     (acong (mul b a) ab bb bb (call 'signed/multiply-commutative b a) (refl bb)))
                              (ring-atoms [['sv-a aa] ['sv-b ab] ['sv-c bb]] (add (add 'sv-a 'sv-b) (add 'sv-b 'sv-c)) (add 'sv-a (add (add 'sv-b 'sv-b) 'sv-c)))])))
        Mf (f/lam [['sm-i nat]] (neg m))
        sumA (chain [(sum A k) (add (sum F k) (sum Mf k)) (add (sum F k) (mul (neg m) N)) (add (mul N m) (mul (neg m) N)) s/zero]
                    [(call 'signed/expr-sum-value-add F Mf k)
                     (acong (sum F k) (sum F k) (sum Mf k) (mul (neg m) N) (refl (sum F k)) (call 'signed/expr-sum-constant-of-nat (neg m) k))
                     (acong (sum F k) (mul N m) (mul (neg m) N) (mul (neg m) N) (sym (mul N m) (sum F k) 'sh-h) (refl (mul (neg m) N)))
                     (ring-atoms [['sw-n N] ['sw-m m]] (add (mul 'sw-n 'sw-m) (mul (neg 'sw-m) 'sw-n)) s/zero)])
        sumAB (chain [(sum AB k) (mul (sum A k) b) (mul s/zero b) s/zero]
                     [(sym (mul (sum A k) b) (sum AB k) (call 'signed/expr-sum-value-scale-right A b k))
                      (mcong (sum A k) s/zero b b sumA (refl b))
                      (ring-atoms [['sx-b b]] (mul s/zero 'sx-b) s/zero)])
        sumQ (chain [(sum Q k) (add (add (sum AB k) (sum AB k)) (mul bb N)) (mul N bb)]
                    [(trans (sum Q k) (add (sum ABAB k) (sum BB k)) (add (add (sum AB k) (sum AB k)) (mul bb N))
                            (call 'signed/expr-sum-value-add ABAB BB k)
                            (acong (sum ABAB k) (add (sum AB k) (sum AB k)) (sum BB k) (mul bb N) (call 'signed/expr-sum-value-add AB AB k)
                                   (call 'signed/expr-sum-constant-of-nat bb k)))
                     (chain [(add (add (sum AB k) (sum AB k)) (mul bb N)) (add (add s/zero s/zero) (mul bb N)) (mul bb N) (mul N bb)]
                            [(acong (add (sum AB k) (sum AB k)) (add s/zero s/zero) (mul bb N) (mul bb N) (acong (sum AB k) s/zero (sum AB k) s/zero sumAB sumAB) (refl (mul bb N)))
                             (ring-atoms [['sz-p (mul bb N)]] (add (add s/zero s/zero) 'sz-p) 'sz-p)
                             (call 'signed/multiply-commutative bb N)])])
        TF (devsq-fam F c)
        total (chain [(sum TF k) (sum AQ k) (add (sum AA k) (sum Q k)) (add (sum AA k) (mul N bb))]
                     [(call 'signed/expr-sum-value-respects-equivalence-below TF AQ k term)
                      (call 'signed/expr-sum-value-add AA Q k)
                      (acong (sum AA k) (sum AA k) (sum Q k) (mul N bb) (refl (sum AA k)) sumQ)])]
    (s/spec 'signed/shifted-square-sum
            [[F family] [q nat] [m signed] [c signed] ['sh-h (eqv (mul N m) (sum F k))]]
            (eqv (sum TF k) (add (sum AA k) (mul N bb)))
            total)))

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

(def theorem-specs [shift-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      of-nat/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      distributive/extend-environment
      multiply-associative/extend-environment
      equivalence/extend-environment
      matrix-scale/extend-environment
      (support/extend-with-shared :expr-sum-anova-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
