(ns rainbow.math.lemmas.mccormick-sandwich
  "General lemmas: mccormick sandwich. The mathematical facts the corresponding checks rest on,
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

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn acong [a b c d h k] (s/add-cong a b c d h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (acong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn diff-np [x y h] (le-resp (sub x y) (sub x y) (sub y y) s/zero (refl (sub x y)) (ring (sub y y) s/zero) (call 'signed/add-right-monotone x y (neg y) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn est [a b x y] (sub (add (mul a y) (mul x b)) (mul a b)))

(def under-spec
  (let [[a b x y] '[mu-a mu-b mu-x mu-y] E (est a b x y) P (mul (sub x a) (sub y b))]
    (s/spec 'signed/mccormick-under [['mu-a signed] ['mu-b signed] ['mu-x signed] ['mu-y signed] ['mu-h (le s/zero P)]]
            (le E (mul x y))
            (le-resp (add E s/zero) E (add E P) (mul x y) (ring (add E s/zero) E) (ring (add E P) (mul x y))
                     (call 'signed/add-left-monotone s/zero P E 'mu-h)))))

(def over-spec
  (let [[a b x y] '[mo-a mo-b mo-x mo-y] E (est a b x y) Q (mul (sub a x) (sub y b))]
    (s/spec 'signed/mccormick-over [['mo-a signed] ['mo-b signed] ['mo-x signed] ['mo-y signed] ['mo-h (le s/zero Q)]]
            (le (mul x y) E)
            (le-resp (add (mul x y) s/zero) (mul x y) (add (mul x y) Q) E (ring (add (mul x y) s/zero) (mul x y)) (ring (add (mul x y) Q) E)
                     (call 'signed/add-left-monotone s/zero Q (mul x y) 'mo-h)))))

(defn coord-prop [X Y XL XU YL YU L H]
  (let [u1 (est XL YL X Y) u2 (est XU YU X Y) o1 (est XU YL X Y) o2 (est XL YU X Y) XY (mul X Y)]
    (pconj (pconj (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)))
           (pconj (pconj (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)))
                  (pconj (le L XY) (le XY H))))))

(def coordinate-spec
  (let [[X Y XL XU YL YU L H] '[mt-x mt-y mt-xl mt-xu mt-yl mt-yu mt-lo mt-hi]
        u1 (est XL YL X Y) u2 (est XU YU X Y) o1 (est XU YL X Y) o2 (est XL YU X Y) XY (mul X Y)
        A1 (sub L u1) A2 (sub L u2) B1 (sub o1 H) B2 (sub o2 H)
        hyps [['mt-g0 (le XL X)] ['mt-g1 (le X XU)] ['mt-g2 (le YL Y)] ['mt-g3 (le Y YU)]
              ['mt-g4 (le u1 L)] ['mt-g5 (le u2 L)] ['mt-g6 (eqv (mul A1 A2) s/zero)]
              ['mt-g8 (le H o1)] ['mt-g9 (le H o2)] ['mt-g10 (eqv (mul B1 B2) s/zero)]]
        ldisj (cases (eqv A1 s/zero) (eqv A2 s/zero) (disj (eqv L u1) (eqv L u2)) (call 'signed/multiply-zero-split A1 A2 'mt-g6)
                     (f/lam [['mk-a (eqv A1 s/zero)]] (inl (eqv L u1) (eqv L u2) (sym u1 L (from-diff u1 L 'mk-a))))
                     (f/lam [['mk-b (eqv A2 s/zero)]] (inr (eqv L u1) (eqv L u2) (sym u2 L (from-diff u2 L 'mk-b)))))
        hdisj (cases (eqv B1 s/zero) (eqv B2 s/zero) (disj (eqv H o1) (eqv H o2)) (call 'signed/multiply-zero-split B1 B2 'mt-g10)
                     (f/lam [['ml-a (eqv B1 s/zero)]] (inl (eqv H o1) (eqv H o2) (from-diff H o1 'ml-a)))
                     (f/lam [['ml-b (eqv B2 s/zero)]] (inr (eqv H o1) (eqv H o2) (from-diff H o2 'ml-b))))
        u1-xy (call 'signed/mccormick-under XL YL X Y (nn-prod (sub X XL) (sub Y YL) (diff-nn XL X 'mt-g0) (diff-nn YL Y 'mt-g2)))
        u2-xy (call 'signed/mccormick-under XU YU X Y
                    (call 'signed/nonpositive-product-nonnegative (sub X XU) (sub Y YU) (diff-np X XU 'mt-g1) (diff-np Y YU 'mt-g3)))
        xy-o1 (call 'signed/mccormick-over XU YL X Y (nn-prod (sub XU X) (sub Y YL) (diff-nn X XU 'mt-g1) (diff-nn YL Y 'mt-g2)))
        xy-o2 (call 'signed/mccormick-over XL YU X Y
                    (call 'signed/nonpositive-product-nonnegative (sub XL X) (sub Y YU) (diff-np XL X 'mt-g0) (diff-np Y YU 'mt-g3)))
        lo-xy (cases (eqv L u1) (eqv L u2) (le L XY) ldisj
                     (f/lam [['mm-1 (eqv L u1)]] (le-resp u1 L XY XY (sym L u1 'mm-1) (refl XY) u1-xy))
                     (f/lam [['mm-2 (eqv L u2)]] (le-resp u2 L XY XY (sym L u2 'mm-2) (refl XY) u2-xy)))
        xy-hi (cases (eqv H o1) (eqv H o2) (le XY H) hdisj
                     (f/lam [['mn-1 (eqv H o1)]] (le-resp XY XY o1 H (refl XY) (sym H o1 'mn-1) xy-o1))
                     (f/lam [['mn-2 (eqv H o2)]] (le-resp XY XY o2 H (refl XY) (sym H o2 'mn-2) xy-o2)))
        LP (pconj (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)))
        HP (pconj (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)))
        SP (pconj (le L XY) (le XY H))]
    (s/spec 'signed/mccormick-coordinate
            (into [['mt-x signed] ['mt-y signed] ['mt-xl signed] ['mt-xu signed] ['mt-yl signed] ['mt-yu signed] ['mt-lo signed] ['mt-hi signed]] hyps)
            (coord-prop X Y XL XU YL YU L H)
            (conjoin LP (pconj HP SP)
                     (conjoin (disj (eqv L u1) (eqv L u2)) (pconj (le u1 L) (le u2 L)) ldisj (conjoin (le u1 L) (le u2 L) 'mt-g4 'mt-g5))
                     (conjoin HP SP
                              (conjoin (disj (eqv H o1) (eqv H o2)) (pconj (le H o1) (le H o2)) hdisj (conjoin (le H o1) (le H o2) 'mt-g8 'mt-g9))
                              (conjoin (le L XY) (le XY H) lo-xy xy-hi))))))

(defn coord-args [{:keys [x y xL xU yL yU lo hi]} i] (mapv #(at % i) [x y xL xU yL yU lo hi]))

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

(def theorem-specs [under-spec over-spec coordinate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-nonzero/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-mccormick-sandwich theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
