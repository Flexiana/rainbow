(ns rainbow.math.lemmas.edf-readings
  "General lemmas: edf readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
            [rainbow.math.lemmas.payasbid-readings :as pab]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.rational.signed.one-hot-unique :as one-hot-unique]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
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

(defn lt [x y] (call 'signed/less-than x y))

(defn kc-fam [kf Cf] (f/lam [['kc-i nat]] (mul (at kf 'kc-i) (at Cf 'kc-i))))

(defn demand-hyp [kf Tf L n] (s/all-below n #(le (mul (at kf %) (at Tf %)) L)))

(def demand-spec
  (let [[Cf Tf uf kf n U L] '[ed-c ed-t ed-u ed-k ed-n ed-uu ed-l]
        UL (f/lam [['ul-i nat]] (mul (at uf 'ul-i) L))
        per (f/lam [['dp-i nat] ['dp-h (below 'dp-i n)]]
                   (let [i 'dp-i h 'dp-h k (at kf i) C (at Cf i) T (at Tf i) u (at uf i) kT (mul k T)]
                     (le-resp (mul u kT) (mul k C) (mul u L) (mul u L)
                              (sym (mul k C) (mul u kT)
                                   (chain [(mul k C) (mul k (mul u T)) (mul (mul k u) T) (mul (mul u k) T) (mul u kT)]
                                          [(mcong k k C (mul u T) (refl k) (sym (mul u T) C (at 'ed-hc i h)))
                                           (sym (mul (mul k u) T) (mul k (mul u T)) (call 'signed/multiply-associative k u T))
                                           (mcong (mul k u) (mul u k) T T (call 'signed/multiply-commutative k u) (refl T))
                                           (call 'signed/multiply-associative u k T)]))
                              (refl (mul u L))
                              (call 'signed/multiply-left-monotone u kT L (at 'ed-hu i h) (at 'ed-hk i h)))))
        sUL (chain [(sum UL n) (mul (sum uf n) L) (mul U L)]
                   [(sym (mul (sum uf n) L) (sum UL n) (call 'signed/expr-sum-value-scale-right uf L n))
                    (mcong (sum uf n) U L L (sym U (sum uf n) 'ed-hsum) (refl L))])
        ul-le (le-resp (mul U L) (mul U L) (mul one L) L (refl (mul U L)) (call 'signed/multiply-one-left L)
                       (call 'signed/scaled-term-at-most L U one 'ed-hl 'ed-h1))]
    (s/spec 'signed/edf-demand-bound
            [[Cf family] [Tf family] [uf family] [kf family] [n nat] [U signed] [L signed]
             ['ed-hu (s/all-below n #(le s/zero (at uf %)))]
             ['ed-hc (s/all-below n #(eqv (mul (at uf %) (at Tf %)) (at Cf %)))]
             ['ed-hsum (eqv U (sum uf n))] ['ed-h1 (le U one)]
             ['ed-hk (demand-hyp kf Tf L n)] ['ed-hl (le s/zero L)]]
            (le (sum (kc-fam kf Cf) n) L)
            (call 'signed/at-most-transitive (sum (kc-fam kf Cf) n) (mul U L) L
                  (le-resp (sum (kc-fam kf Cf) n) (sum (kc-fam kf Cf) n) (sum UL n) (mul U L) (refl (sum (kc-fam kf Cf) n)) sUL
                           (call 'signed/expr-sum-value-monotone-below (kc-fam kf Cf) UL n per))
                  ul-le))))

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

(def borrowed-specs [hhi/positive-spec pab/scaled-term-spec mmck/cancel-positive-spec mmck/successor-positive-spec pcmax/cancel-order-spec])

(def theorem-specs [demand-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      dot-negate/extend-environment
      distributive/extend-environment
      unit-laws/extend-environment
      multiply-associative/extend-environment
      equivalence/extend-environment
      matrix-scale/extend-environment
      one-hot-unique/extend-environment
      (support/extend-with-shared :expr-sum-edf-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
