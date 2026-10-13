(ns rainbow.math.sums.bpath-cut
  "Cut/exit proof support for bottleneck paths. All weights are signed; no nonnegative
  bottleneck premise. New lemmas over unchanged sums and selector definitions."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.one-hot-factor :as factor]
            [rainbow.math.rational.signed.one-hot-selects :as select]))
(def tl [:succ [:zero]])
(def pl [:zero])
(def matrix (f/arrow nat family))
(defn both [P Q] (call 'proposition/conjunction P Q))
(defn pair [P Q p q] (call 'proposition/conjoin P Q p q))
(defn left [P Q h] (call 'proposition/left P Q h))
(defn right [P Q h] (call 'proposition/right P Q h))
(defn exists [pred] (f/app (f/const* 'proposition/existence [tl]) nat pred))
(defn witness [pred value proof] (f/app (f/const* 'proposition/witness [tl]) nat pred value proof))
(defn bit [x] (eqv (mul x (a/sub a/one x)) s/zero))
(defn all2 [n body]
  (f/forall [['bc-u nat] ['bc-hu (below 'bc-u n)] ['bc-v nat] ['bc-hv (below 'bc-v n)]] (body 'bc-u 'bc-v)))
(defn row [P t] (factor/row P t))
(defn side [B S n] (factor/selected B S n))
(defn weight [A B G n] (factor/double-weighted A B G n n))
(defn bit-to-cases [x h] (call 'signed/zero-one-of-boolean-polynomial x h))
(defn bits-nonnegative [B n h]
  (f/lam [['bc-idx nat] ['bc-bound (below 'bc-idx n)]]
    (call 'signed/zero-one-nonnegative (at B 'bc-idx) (at h 'bc-idx 'bc-bound))))
(defn bits-cases [B n h]
  (f/lam [['bc-idx nat] ['bc-bound (below 'bc-idx n)]]
    (bit-to-cases (at B 'bc-idx) (at h 'bc-idx 'bc-bound))))
(defn selects [B n bits unit]
  (call 'signed/one-hot-selects B n (bits-nonnegative B n bits) (bits-cases B n bits) unit))
(defn reads [B n i]
  (f/forall [['bc-values family]] (eqv (side B 'bc-values n) (at 'bc-values i))))
(defn selected [B n i] (both (below i n) (both (eqv (at B i) a/one) (reads B n i))))
(defn selected-bound [B n i h]
  (left (below i n) (both (eqv (at B i) a/one) (reads B n i)) h))
(defn selected-reads [B n i h]
  (right (eqv (at B i) a/one) (reads B n i)
    (right (below i n) (both (eqv (at B i) a/one) (reads B n i)) h)))
(defn bit-respects [x y xy hx]
  (trans (mul y (a/sub a/one y)) (mul x (a/sub a/one x)) s/zero
    (a/mul-cong y x (a/sub a/one y) (a/sub a/one x) (sym x y xy)
      (s/add-cong a/one a/one (a/neg y) (a/neg x) (refl a/one) (a/neg-cong y x (sym x y xy)))) hx))
(def selector-bit-spec
  (let [B 'bc-B S 'bc-S n 'bc-n value (side B S n) goal (bit value)]
    (s/spec 'signed/one-hot-selects-binary-value
      [[B family] [S family] [n nat] ['bc-bits (factor/binary B n)]
       ['bc-unit (eqv (sum B n) a/one)] ['bc-values-bits (factor/binary S n)]]
      goal
      (at (selects B n 'bc-bits 'bc-unit) goal
        (f/lam [['bc-picked nat] ['bc-evidence (selected B n 'bc-picked)]]
          (let [hread (at (selected-reads B n 'bc-picked 'bc-evidence) S)
                hb (at 'bc-values-bits 'bc-picked (selected-bound B n 'bc-picked 'bc-evidence))]
            (bit-respects (at S 'bc-picked) value (sym value (at S 'bc-picked) hread) hb)))))))
(defn exit-predicate [Z M]
  (f/lam [['bc-exit nat]]
    (both (below 'bc-exit M)
      (both (eqv (at Z 'bc-exit) a/one) (eqv (at Z (s/succ 'bc-exit)) s/zero)))))
(defn exit-binders [Z M]
  [['bc-seq-bits (factor/binary Z (s/succ M))]
   ['bc-start (eqv (at Z s/nz) a/one)] ['bc-end (eqv (at Z M) s/zero)]])
(def exit-spec
  (let [Z 'bc-Z M 'bc-M
        claim (fn [k] (f/forall (exit-binders Z k) (exists (exit-predicate Z k))))]
    (s/spec 'signed/binary-sequence-exit [[Z family] [M nat]] (claim M)
      (f/app (f/const* 'data/Nat.rec [pl])
        (f/lam [['bc-length nat]] (claim 'bc-length))
        (f/lam (exit-binders Z s/nz)
          (call 'proposition/explode (exists (exit-predicate Z s/nz))
            (call 'signed/one-not-equivalent-zero
              (trans a/one (at Z s/nz) s/zero (sym (at Z s/nz) a/one 'bc-start) 'bc-end))))
        (f/lam [['bc-k nat] ['bc-ih (claim 'bc-k)]]
          (f/lam (exit-binders Z (s/succ 'bc-k))
            (let [k 'bc-k z (at Z k) goal (exists (exit-predicate Z (s/succ k)))
                  kz (eqv z s/zero) ko (eqv z a/one)
                  old (exists (exit-predicate Z k))
                  prefix (f/lam [['bc-i nat] ['bc-hi (below 'bc-i (s/succ k))]]
                           (at 'bc-seq-bits 'bc-i (s/weaken 'bc-i (s/succ k) 'bc-hi)))]
              (a/cases kz ko goal
                (bit-to-cases z (at 'bc-seq-bits k (s/weaken k (s/succ k) (s/self-below k))))
                (f/lam [['bc-kzero kz]]
                  (at (at 'bc-ih prefix 'bc-start 'bc-kzero) goal
                    (f/lam [['bc-old nat] ['bc-old-proof (at (exit-predicate Z k) 'bc-old)]]
                      (let [tail (both (eqv (at Z 'bc-old) a/one) (eqv (at Z (s/succ 'bc-old)) s/zero))]
                        (witness (exit-predicate Z (s/succ k)) 'bc-old
                          (pair (below 'bc-old (s/succ k)) tail
                            (s/weaken 'bc-old k (left (below 'bc-old k) tail 'bc-old-proof))
                            (right (below 'bc-old k) tail 'bc-old-proof)))))))
                (f/lam [['bc-kone ko]]
                  (witness (exit-predicate Z (s/succ k)) k
                    (pair (below k (s/succ k)) (both ko (eqv (at Z (s/succ k)) s/zero))
                      (s/self-below k) (pair ko (eqv (at Z (s/succ k)) s/zero) 'bc-kone 'bc-end))))))))
        M))))
(defn crossing [E S threshold W u v]
  (mul (mul (at E u v) (at S u))
       (mul (a/sub a/one (at S v)) (a/sub threshold (at W u v)))))
(def difference-bound-spec
  (s/spec 'signed/subtract-nonpositive-implies-at-most
    [['bc-x signed] ['bc-y signed] ['bc-order (le (a/sub 'bc-x 'bc-y) s/zero)]]
    (le 'bc-x 'bc-y)
    (s/le-transport (s/add (a/sub 'bc-x 'bc-y) 'bc-y) 'bc-x
      (s/add s/zero 'bc-y) 'bc-y
      (a/ring-eq (s/add (a/sub 'bc-x 'bc-y) 'bc-y) 'bc-x)
      (a/ring-eq (s/add s/zero 'bc-y) 'bc-y)
      (call 'signed/add-right-monotone (a/sub 'bc-x 'bc-y) s/zero 'bc-y 'bc-order))))
(def cut-step-spec
  (let [A 'bc-A B 'bc-B E 'bc-E S 'bc-S W 'bc-W n 'bc-n threshold 'bc-threshold
        result (le threshold (weight A B W n))]
    (s/spec 'signed/one-hot-cut-exit-weight-bound
      [[A family] [B family] [E matrix] [S family] [W matrix] [n nat] [threshold signed]
       ['bc-abits (factor/binary A n)] ['bc-aunit (eqv (sum A n) a/one)]
       ['bc-bbits (factor/binary B n)] ['bc-bunit (eqv (sum B n) a/one)]
       ['bc-edge (eqv (weight A B E n) a/one)]
       ['bc-inside (eqv (side A S n) a/one)] ['bc-outside (eqv (side B S n) s/zero)]
       ['bc-crossing (all2 n #(le (crossing E S threshold W %1 %2) s/zero))]]
      result
      (at (selects A n 'bc-abits 'bc-aunit) result
        (f/lam [['bc-u nat] ['bc-au (selected A n 'bc-u)]]
          (at (selects B n 'bc-bbits 'bc-bunit) result
            (f/lam [['bc-v nat] ['bc-bv (selected B n 'bc-v)]]
              (let [u 'bc-u v 'bc-v ra (selected-reads A n u 'bc-au) rb (selected-reads B n v 'bc-bv)
                    picked (fn [G]
                             (let [inner (f/lam [['bc-row nat]] (side B (row G 'bc-row) n))]
                               (trans (weight A B G n) (side B (row G u) n) (at G u v)
                                 (at ra inner) (at rb (row G u)))))
                    e1 (trans (at E u v) (weight A B E n) a/one (sym (weight A B E n) (at E u v) (picked E)) 'bc-edge)
                    su1 (trans (at S u) (side A S n) a/one (sym (side A S n) (at S u) (at ra S)) 'bc-inside)
                    sv0 (trans (at S v) (side B S n) s/zero (sym (side B S n) (at S v) (at rb S)) 'bc-outside)
                    diff (a/sub threshold (at W u v))
                    c (crossing E S threshold W u v)
                    unit-form (mul (mul a/one a/one) (mul (a/sub a/one s/zero) diff))
                    c-diff (trans c unit-form diff
                             (a/mul-cong (mul (at E u v) (at S u)) (mul a/one a/one)
                               (mul (a/sub a/one (at S v)) diff) (mul (a/sub a/one s/zero) diff)
                               (a/mul-cong (at E u v) a/one (at S u) a/one e1 su1)
                               (a/mul-cong (a/sub a/one (at S v)) (a/sub a/one s/zero) diff diff
                                 (s/add-cong a/one a/one (a/neg (at S v)) (a/neg s/zero) (refl a/one)
                                   (a/neg-cong (at S v) s/zero sv0)) (refl diff)))
                             (a/ring-eq unit-form diff))
                    diff-le (s/le-transport c diff s/zero s/zero c-diff (refl s/zero)
                              (at 'bc-crossing u (selected-bound A n u 'bc-au) v (selected-bound B n v 'bc-bv)))
                    bound (call 'signed/subtract-nonpositive-implies-at-most threshold (at W u v) diff-le)]
                (s/le-transport threshold threshold (at W u v) (weight A B W n)
                  (refl threshold) (sym (weight A B W n) (at W u v) (picked W)) bound)))))))))
(def theorem-specs [selector-bit-spec exit-spec difference-bound-spec cut-step-spec])
(defn extend-environment [env]
  (reduce (fn [e spec]
            (println :bpath-cut :installing (:name spec)) (flush)
            (support/add-spec-shared e :expr-sum-bpath-cut spec))
          (factor/extend-environment env) theorem-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
