(ns rainbow.math.lemmas.knn-reading
  "General lemmas: knn reading. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.abc-class :as abc]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(defn gap-le [x y h]
  (le-resp (add (sub x y) y) x (add s/zero y) y (ring (add (sub x y) y) x) (ring (add s/zero y) y)
           (call 'signed/add-right-monotone (sub x y) s/zero y h)))

(defn row [d z n i] (sum (f/lam [['kn-j nat]] (mul (sub one (at z 'kn-j)) (abc/strict-ind (at d 'kn-j) (at d i)))) n))

(def nearer-spec
  (let [d 'kn-d z 'kn-z n 'kn-n i 'kn-i j 'kn-j di (at d i) dj (at d j) zi (at z i) zj (at z j)
        R (row d z n i)
        T (f/lam [['kn-j nat]] (mul (sub one (at z 'kn-j)) (abc/strict-ind (at d 'kn-j) di)))
        r0 (a/chain R [(mul one R) (sym (mul one R) R (one-times R))]
                    [(mul zi R) (mcong one zi R R (sym zi one 'kn-zi) (refl R))]
                    [s/zero (at 'kn-top i 'kn-hi)])
        tnn (f/lam [['kt-j nat] ['kt-h (below 'kt-j n)]]
                   (nonneg-prod (sub one (at z 'kt-j)) (abc/strict-ind (at d 'kt-j) di)
                                (call 'signed/one-minus-nonnegative (at z 'kt-j) (call 'signed/zero-one-at-most-one (at z 'kt-j) (at 'kn-01 'kt-j 'kt-h)))
                                (call 'signed/strict-indicator-nonnegative (at d 'kt-j) di)))
        each (call 'signed/expr-sum-value-nonnegative-terms-zero T n tnn r0)
        I (abc/strict-ind dj di)
        I0 (a/chain I [(mul one I) (sym (mul one I) I (one-times I))]
                    [(mul (sub one s/zero) I) (mcong one (sub one s/zero) I I (ring one (sub one s/zero)) (refl I))]
                    [(mul (sub one zj) I) (mcong (sub one s/zero) (sub one zj) I I
                                                 (s/add-cong one one (neg s/zero) (neg zj) (refl one) (a/neg-cong s/zero zj (sym zj s/zero 'kn-zj)))
                                                 (refl I))]
                    [s/zero (at each j 'kn-hj)])]
    (s/spec 'signed/knn-selected-nearer
            [['kn-d family] ['kn-z family] ['kn-n nat]
             ['kn-01 (s/all-below n #(zero-one (at z %)))]
             ['kn-top (s/all-below n #(eqv (mul (at z %) (row d z n %)) s/zero))]
             ['kn-i nat] ['kn-hi (below i n)] ['kn-j nat] ['kn-hj (below j n)]
             ['kn-zi (eqv zi one)] ['kn-zj (eqv zj s/zero)]]
            (le di dj)
            (call 'signed/strict-indicator-zero-order dj di I0))))

(defn majority-prop [y k tC] (pconj (f/arrow (eqv y one) (le k tC)) (f/arrow (eqv y s/zero) (le tC k))))

(def majority-spec
  (let [y 'mj-y k 'mj-k tC 'mj-c]
    (s/spec 'signed/knn-majority
            [['mj-y signed] ['mj-k signed] ['mj-c signed]
             ['mj-1 (le (mul y (add k (neg tC))) s/zero)]
             ['mj-0 (le (mul (add one (neg y)) (add tC (neg k))) s/zero)]]
            (majority-prop y k tC)
            (conjoin (f/arrow (eqv y one) (le k tC)) (f/arrow (eqv y s/zero) (le tC k))
                     (f/lam [['mj-y1 (eqv y one)]]
                            (gap-le k tC (le-resp (mul y (sub k tC)) (sub k tC) s/zero s/zero
                                                  (a/chain (mul y (sub k tC)) [(mul one (sub k tC)) (mcong y one (sub k tC) (sub k tC) 'mj-y1 (refl (sub k tC)))]
                                                           [(sub k tC) (one-times (sub k tC))])
                                                  (refl s/zero) 'mj-1)))
                     (f/lam [['mj-y0 (eqv y s/zero)]]
                            (gap-le tC k (le-resp (mul (sub one y) (sub tC k)) (sub tC k) s/zero s/zero
                                                  (a/chain (mul (sub one y) (sub tC k))
                                                           [(mul (sub one s/zero) (sub tC k)) (mcong (sub one y) (sub one s/zero) (sub tC k) (sub tC k)
                                                                                                     (s/add-cong one one (neg y) (neg s/zero) (refl one) (a/neg-cong y s/zero 'mj-y0))
                                                                                                     (refl (sub tC k)))]
                                                           [(mul one (sub tC k)) (mcong (sub one s/zero) one (sub tC k) (sub tC k) (ring (sub one s/zero) one) (refl (sub tC k)))]
                                                           [(sub tC k) (one-times (sub tC k))])
                                                  (refl s/zero) 'mj-0)))))))

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

(def theorem-specs [nearer-spec majority-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      abc/extend-environment
      of-nat/extend-environment
      (support/extend-with-shared :expr-sum-knn-reading theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
