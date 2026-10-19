(ns rainbow.math.sums.indicator-zero
  "A zero sum of strict-violation indicators means every weak inequality holds."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.strict-indicator :as strict]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def zero-order-spec
  (let [D (call 'signed/decide-at-most 'x 'y) goal (le 'x 'y)]
    (s/spec 'signed/zero-strict-indicator-implies-order
      [['x signed] ['y signed] ['zero (eqv (strict/indicator 'x 'y) s/zero)]] goal
      (at (#'cea/by-bit D #(f/arrow (eqv (strict/selected %) s/zero) goal)
            (fn [_] (f/lam [['bad (eqv b/one s/zero)]] (call 'proposition/explode goal
                                                       (call 'signed/one-not-at-most-zero (a/eq-le b/one s/zero 'bad)))))
            (fn [h] (f/lam [['ignored (eqv s/zero s/zero)]] (call 'signed/decide-at-most-true-sound 'x 'y h))) 'decision) 'zero))))
(def order-zero-spec
  (let [D (call 'signed/decide-at-most 'x 'y) h (call 'signed/decide-at-most-true-complete 'x 'y 'order)]
    (s/spec 'signed/order-implies-zero-strict-indicator [['x signed] ['y signed] ['order (le 'x 'y)]]
      (eqv (strict/indicator 'x 'y) s/zero)
      (f/app (f/const* 'equality/substitution [strict/U]) strict/bool strict/true-bit D
        (f/app (f/const* 'equality/symmetric [strict/U]) strict/bool D strict/true-bit h)
        (f/lam [['bit strict/bool]] (eqv (strict/selected 'bit) s/zero)) (refl s/zero)))))
(defn indicators [F G] (let [i (gensym "index")] (f/lam [[i nat]] (strict/indicator (at F i) (at G i)))))
(def forward-spec
  (let [I (indicators 'F 'G) nn (f/lam [['i nat] ['hi (s/below 'i 'n)]] (call 'signed/strict-comparison-indicator-nonnegative (at 'F 'i) (at 'G 'i)))]
    (s/spec 'signed/zero-strict-indicator-sum-implies-orders
      [['F family] ['G family] ['n nat] ['sum (le (sum I 'n) s/zero)]]
      (s/all-below 'n #(le (at 'F %) (at 'G %)))
      (f/lam [['i nat] ['hi (s/below 'i 'n)]]
        (call 'signed/zero-strict-indicator-implies-order (at 'F 'i) (at 'G 'i)
          (call 'signed/nonnegative-nonpositive-sum-term-zero I 'n nn 'sum 'i 'hi))))))
(def backward-spec
  (let [I (indicators 'F 'G) Z (f/lam [['ignored nat]] s/zero)]
    (s/spec 'signed/orders-imply-zero-strict-indicator-sum
      [['F family] ['G family] ['n nat] ['orders (s/all-below 'n #(le (at 'F %) (at 'G %)))]]
      (le (sum I 'n) s/zero)
      (a/eq-le (sum I 'n) s/zero
        (s/trans (sum I 'n) (sum Z 'n) s/zero
          (a/sum-cong I Z 'n 'i (fn [i hi] (call 'signed/order-implies-zero-strict-indicator (at 'F i) (at 'G i) (at 'orders i hi))))
          (call 'signed/expr-sum-value-zero 'n))))))
(def theorem-specs [zero-order-spec order-zero-spec forward-spec backward-spec])
(def deps '[rainbow.math.sums.strict-indicator rainbow.math.sums.binary-conflicts])
(defn install [env] (support/extend-with env :expr-sum-indicator-zero theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.indicator-zero))
