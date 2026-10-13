(ns rainbow.math.lemmas.reservoir-readings
  "General lemmas: reservoir readings. The mathematical facts the corresponding checks rest on,
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
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]))

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

(defn outflow [I R P] (add I (add (neg R) (neg P))))

(defn step-claim [S S1 I R P K D]
  (pconj (disj (eqv P s/zero) (eqv S1 K)) (pconj (le (add R P) (add S I)) (le s/zero (sub D R)))))

(def step-spec
  (let [[S S1 I R P K D] '[rs-s rs-s1 rs-i rs-r rs-p rs-k rs-d]
        D1 (disj (eqv P s/zero) (eqv S1 K)) G (sub K S1)
        spill (cases (eqv P s/zero) (eqv G s/zero) D1 (call 'signed/multiply-zero-split P G 'rs-hp)
                     (f/lam [['rs-p0 (eqv P s/zero)]] (inl (eqv P s/zero) (eqv S1 K) 'rs-p0))
                     (f/lam [['rs-g0 (eqv G s/zero)]] (inr (eqv P s/zero) (eqv S1 K) (call 'signed/eq-of-difference-zero S1 K 'rs-g0))))
        RP (add R P) flow (add S (outflow I R P))
        hs (chain [(add S1 RP) (add flow RP) (add S I)]
                  [(acong S1 flow RP RP 'rs-hb (refl RP))
                   (ring-atoms [['ra-s S] ['ra-i I] ['ra-r R] ['ra-p P]]
                               (add (add 'ra-s (add 'ra-i (add (neg 'ra-r) (neg 'ra-p)))) (add 'ra-r 'ra-p)) (add 'ra-s 'ra-i))])
        rel (le-resp (add s/zero RP) RP (add S1 RP) (add S I) (ring-atoms [['rz-x RP]] (add s/zero 'rz-x) 'rz-x) hs
                     (call 'signed/add-right-monotone s/zero S1 RP 'rs-hs1))
        short (le-resp (add R (neg R)) s/zero (add D (neg R)) (sub D R) (ring-atoms [['rq-r R]] (add 'rq-r (neg 'rq-r)) s/zero) (refl (sub D R))
                       (call 'signed/add-right-monotone R D (neg R) 'rs-hd))]
    (s/spec 'signed/reservoir-step
            [[S signed] [S1 signed] [I signed] [R signed] [P signed] [K signed] [D signed]
             ['rs-hb (eqv S1 flow)] ['rs-hs1 (le s/zero S1)] ['rs-hp (eqv (mul P G) s/zero)] ['rs-hd (le R D)]]
            (step-claim S S1 I R P K D)
            (conjoin D1 (pconj (le RP (add S I)) (le s/zero (sub D R))) spill
                     (conjoin (le RP (add S I)) (le s/zero (sub D R)) rel short)))))

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

(def theorem-specs [step-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      equivalence/extend-environment
      (support/extend-with-shared :expr-sum-reservoir-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
