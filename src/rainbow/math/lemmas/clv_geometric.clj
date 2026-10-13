(ns rainbow.math.lemmas.clv-geometric
  "General lemmas: clv geometric. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def step-spec
  (let [[r R R1 D D1 E] '[cs-r cs-rr cs-r1 cs-d cs-d1 cs-e]]
    (s/spec 'signed/clv-step
            [['cs-r signed] ['cs-rr signed] ['cs-r1 signed] ['cs-d signed] ['cs-d1 signed] ['cs-e signed]
             ['cs-hr (eqv R1 (mul r R))] ['cs-hd (eqv (mul D1 E) D)]]
            (eqv (mul (mul R1 D1) E) (mul r (mul R D)))
            (a/chain (mul (mul R1 D1) E)
                     [(mul R1 (mul D1 E)) (call 'signed/multiply-associative R1 D1 E)]
                     [(mul (mul r R) D) (mcong R1 (mul r R) (mul D1 E) D 'cs-hr 'cs-hd)]
                     [(mul r (mul R D)) (call 'signed/multiply-associative r R D)]))))

(def telescope-spec
  (let [q 'gt-q E 'gt-e r 'gt-r qt #(at q %)
        lhs (fn [m] (sub (mul (sum q (s/succ m)) E) (mul r (sum q (s/succ m)))))
        rhs (fn [m] (sub (mul (qt s/nz) E) (mul r (qt m))))
        claim (fn [m] (f/forall [['gt-h (s/all-below m #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]] (eqv (lhs m) (rhs m))))]
    (s/spec 'signed/geometric-telescope [['gt-q family] ['gt-e signed] ['gt-r signed] ['gt-n nat]]
            (claim 'gt-n)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['gt-k nat]] (claim 'gt-k))
                   (f/lam [['gt-h (s/all-below s/nz #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]]
                          (let [S1 (add s/zero (qt s/nz))]   ; sum q 1 unfolds to 0 + q_0
                            (ring (sub (mul S1 E) (mul r S1)) (rhs s/nz))))
                   (f/lam [['gt-j nat] ['gt-ih (claim 'gt-j)] ['gt-h (s/all-below (s/succ 'gt-j) #(eqv (mul (qt (s/succ %)) E) (mul r (qt %))))]]
                          (let [j 'gt-j j1 (s/succ j) S (sum q j1) qj (qt j) qj1 (qt j1)
                                weak (f/lam [['gt-i nat] ['gt-il (below 'gt-i j)]] (at 'gt-h 'gt-i (call 'nat/strict-below-weaken 'gt-i j 'gt-il)))
                                prev (at 'gt-ih weak)
                                step (at 'gt-h j (s/self-below j))]
                            ;; (S + q_{j+1}) E - r (S + q_{j+1}) ~ (S E - r S) + (q_{j+1} E - r q_{j+1})
                            ;;   ~ (q_0 E - r q_j) + (r q_j - r q_{j+1}) ~ q_0 E - r q_{j+1}
                            (a/chain (sub (mul (add S qj1) E) (mul r (add S qj1)))   ; sum q (j1 + 1) unfolds to S + q_{j1}
                                     [(add (sub (mul S E) (mul r S)) (sub (mul qj1 E) (mul r qj1))) (ring (sub (mul (add S qj1) E) (mul r (add S qj1))) (add (sub (mul S E) (mul r S)) (sub (mul qj1 E) (mul r qj1))))]
                                     [(add (rhs j) (sub (mul r qj) (mul r qj1)))
                                      (s/add-cong (sub (mul S E) (mul r S)) (rhs j) (sub (mul qj1 E) (mul r qj1)) (sub (mul r qj) (mul r qj1))
                                                  prev (s/add-cong (mul qj1 E) (mul r qj) (neg (mul r qj1)) (neg (mul r qj1)) step (refl (neg (mul r qj1)))))]
                                     [(rhs j1) (ring (add (rhs j) (sub (mul r qj) (mul r qj1))) (rhs j1))])))
                   'gt-n))))

(def scale-spec
  (let [[m S E r X] '[sc-m sc-s sc-e sc-r sc-x]]
    (s/spec 'signed/clv-scale [['sc-m signed] ['sc-s signed] ['sc-e signed] ['sc-r signed] ['sc-x signed] ['sc-h (eqv (sub (mul S E) (mul r S)) X)]]
            (eqv (mul (mul m S) (sub E r)) (mul m X))
            (a/chain (mul (mul m S) (sub E r))
                     [(mul m (sub (mul S E) (mul r S))) (ring (mul (mul m S) (sub E r)) (mul m (sub (mul S E) (mul r S))))]
                     [(mul m X) (mcong m m (sub (mul S E) (mul r S)) X (refl m) 'sc-h)]))))

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

(def theorem-specs [step-spec telescope-spec scale-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      nat-more/extend-environment
      multiply-associative/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-clv-geometric theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
