(ns rainbow.math.sums.one-hot-factor
  "Reusable selection factorization for arbitrary signed values. Only the inner
  selector is one-hot; the outer weights may have any sign or total. Bridges to
  the existing selector and operation-preservation theorem, with no new induction."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.permutation-invariant :as pi]
            [rainbow.math.rational.signed.one-hot-selects :as select]
            [rainbow.math.lemmas.kmeans-nearest :as bits]))
(def matrix (f/arrow nat family))
(defn binary [B n]
  (s/all-below n #(eqv (mul (at B %) (a/sub a/one (at B %))) s/zero)))
(defn weighted [B F] (f/lam [['oh-v nat]] (mul (at B 'oh-v) (at F 'oh-v))))
(defn selected [B F n] (sum (weighted B F) n))
(defn product [F G] (f/lam [['oh-v nat]] (mul (at F 'oh-v) (at G 'oh-v))))
(defn row [G u] (f/lam [['oh-v nat]] (at G u 'oh-v)))
(defn double-weighted [A B G m n]
  (sum (f/lam [['oh-u nat]] (mul (at A 'oh-u) (selected B (row G 'oh-u) n))) m))
(defn column-product [F G]
  (f/lam [['oh-u nat] ['oh-v nat]] (mul (at F 'oh-v) (at G 'oh-u 'oh-v))))
(defn assumptions [B n]
  [['oh-bits (binary B n)] ['oh-unit (eqv (sum B n) a/one)]])
(def product-spec
  (let [B 'oh-B F 'oh-F G 'oh-G n 'oh-n
        left (selected B (product F G) n)
        right (mul (selected B F n) (selected B G n))
        multiplication (f/const* 'signed/multiply [])
        respects (f/lam [['oh-x signed] ['oh-y signed] ['oh-z signed] ['oh-w signed]
                          ['oh-xz (eqv 'oh-x 'oh-z)] ['oh-yw (eqv 'oh-y 'oh-w)]]
                   (a/mul-cong 'oh-x 'oh-z 'oh-y 'oh-w 'oh-xz 'oh-yw))
        nonnegative (f/lam [['oh-i nat] ['oh-hi (s/below 'oh-i n)]]
                      (call 'signed/zero-one-nonnegative (at B 'oh-i) (at 'oh-bits 'oh-i 'oh-hi)))
        disjunction (f/lam [['oh-i nat] ['oh-hi (s/below 'oh-i n)]]
                      (call 'signed/zero-one-of-boolean-polynomial (at B 'oh-i) (at 'oh-bits 'oh-i 'oh-hi)))]
    (s/spec 'signed/expr-sum-one-hot-product
      (into [[B family] [F family] [G family] [n nat]] (assumptions B n))
      (eqv left right)
      (sym right left
        (call 'signed/one-hot-preserves-binary-operation B F G multiplication n
          respects nonnegative disjunction 'oh-unit)))))
(def right-factor-spec
  (let [A 'oh-A B 'oh-B F 'oh-F G 'oh-G m 'oh-m n 'oh-n
        selected-F (selected B F n)
        source (f/lam [['oh-u nat]] (mul (at A 'oh-u) (selected B (row (column-product F G) 'oh-u) n)))
        base (f/lam [['oh-u nat]] (mul (at A 'oh-u) (selected B (row G 'oh-u) n)))
        factored (f/lam [['oh-u nat]] (mul selected-F (at base 'oh-u)))
        left (double-weighted A B (column-product F G) m n)
        right (mul selected-F (double-weighted A B G m n))]
    (s/spec 'signed/expr-sum-one-hot-right-factor
      (into [[A family] [B family] [F family] [G matrix] [m nat] [n nat]] (assumptions B n))
      (eqv left right)
      (s/trans left (sum factored m) right
        (a/sum-cong source factored m 'oh-at
          (fn [u _]
            (let [r (row G u) rsum (selected B r n) av (at A u)
                  l (mul av (selected B (product F r) n))
                  mid (mul av (mul selected-F rsum))]
              (s/trans l mid (mul selected-F (mul av rsum))
                (a/mul-cong av av (selected B (product F r) n) (mul selected-F rsum)
                  (refl av) (call 'signed/expr-sum-one-hot-product B F r n 'oh-bits 'oh-unit))
                (a/ring-eq mid (mul selected-F (mul av rsum)))))))
        (sym right (sum factored m) (call 'signed/expr-sum-value-scale-left base selected-F m))))))
(def theorem-specs [product-spec right-factor-spec])
(defn extend-environment [env]
  (let [base (-> env a/extend-environment select/extend-environment)
        ready (reduce #(support/add-spec-shared %1 :expr-sum-one-hot-factor %2)
                      base [bits/zero-one-nonneg-spec pi/one-hot-operation-spec])]
    (reduce (fn [e spec]
              (println :one-hot-factor :installing (:name spec)) (flush)
              (support/add-spec-shared e :expr-sum-one-hot-factor spec)) ready theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
