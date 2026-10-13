(ns rainbow.math.lemmas.unifpx-readings
  "General lemmas: unifpx readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-nonzero :as multiply-nonzero]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

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

(def prefix-units-spec
  (let [x 'pu-x q 'pu-q Q 'pu-Q r 'pu-r S 'pu-S M 'pu-M M1 (s/succ M)
        le-add (fn [a1 b1 c1 d1 hab hcd]
                 (le-trans (add a1 c1) (add b1 c1) (add b1 d1) (call 'signed/add-right-monotone a1 b1 c1 hab)
                           (le-resp (add c1 b1) (add b1 c1) (add d1 b1) (add b1 d1) (ring (add c1 b1) (add b1 c1)) (ring (add d1 b1) (add b1 d1))
                                    (call 'signed/add-right-monotone c1 d1 b1 hcd))))
        rem-of (fn [j] (sub S (at Q j)))
        units-claim (fn [t] (f/forall [['ua-h (below t M1)]] (pconj (le (sum x t) (sum q t)) (le (sum x t) S))))
        units (f/app (f/app (f/const* 'data/Nat.rec [prop-level])
                            (f/lam [['ua-t nat]] (units-claim 'ua-t))
                            (f/lam [['ua-h (below s/nz M1)]]
                                   (conjoin (le (sum x s/nz) (sum q s/nz)) (le (sum x s/nz) S) (a/eq-le s/zero s/zero (refl s/zero)) 'pu-hS))
                            (f/lam [['ub-s nat] ['ub-ih (units-claim 'ub-s)] ['ub-h (below (s/succ 'ub-s) M1)]]
                                   (let [j 'ub-s hs (call 'nat/at-most-successor-cancel-local (s/succ j) M 'ub-h)
                                         ih (at 'ub-ih (call 'nat/strict-below-weaken j M hs))
                                         SX (sum x j) SQ (sum q j) xj (at x j) qj (at q j) rj (at r j)
                                         ih1 (call 'proposition/left (le SX SQ) (le SX S) ih)
                                         ih2 (call 'proposition/right (le SX SQ) (le SX S) ih)
                                         L (eqv rj s/zero) Rt (eqv rj (rem-of j))
                                         goal (le (add SX xj) S)]
                                     (conjoin (le (add SX xj) (add SQ qj)) goal
                                              (le-add SX SQ xj qj ih1 (at 'pu-hxq j hs))
                                              (cases L Rt goal (at 'pu-hr j hs)
                                                     (f/lam [['uc-z L]]
                                                            (let [x-np (le-resp xj xj rj s/zero (refl xj) 'uc-z (at 'pu-hxr j hs))]
                                                              (le-trans (add SX xj) SX S
                                                                        (le-resp (add SX xj) (add SX xj) (add SX s/zero) SX (refl (add SX xj)) (ring (add SX s/zero) SX)
                                                                                 (le-add SX SX xj s/zero (a/eq-le SX SX (refl SX)) x-np))
                                                                        ih2)))
                                                     (f/lam [['uc-r Rt]]
                                                            (let [Qj (at Q j) x-rem (le-resp xj xj rj (rem-of j) (refl xj) 'uc-r (at 'pu-hxr j hs))
                                                                  q-eq (at 'pu-hQ j hs)]
                                                              (le-resp (add SX xj) (add SX xj) (add SQ (rem-of j)) S (refl (add SX xj))
                                                                       (a/chain (add SQ (rem-of j)) [(add Qj (rem-of j)) (s/add-cong SQ Qj (rem-of j) (rem-of j) (sym Qj SQ q-eq) (refl (rem-of j)))]
                                                                                [S (ring (add Qj (rem-of j)) S)])
                                                                       (le-add SX SQ xj (rem-of j) ih1 x-rem))))))))
                            M)
                     (s/self-below M))]
    (s/spec 'signed/prefix-units-bound
            [['pu-x family] ['pu-q family] ['pu-Q family] ['pu-r family] ['pu-S signed] ['pu-M nat]
             ['pu-hxq (s/all-below M (fn [j] (le (at x j) (at q j))))]
             ['pu-hxr (s/all-below M (fn [j] (le (at x j) (at r j))))]
             ['pu-hr (s/all-below M (fn [j] (disj (eqv (at r j) s/zero) (eqv (at r j) (rem-of j)))))]
             ['pu-hQ (s/all-below M (fn [j] (eqv (at Q j) (sum q j))))]
             ['pu-hS (le s/zero S)]]
            (pconj (le (sum x M) (sum q M)) (le (sum x M) S))
            units)))

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

(def theorem-specs [prefix-units-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-unifpx-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
