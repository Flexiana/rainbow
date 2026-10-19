(ns rainbow.math.sums.pareto-mask
  "The Pareto penalty mask is equivalent to absence of strict gain under componentwise dominance."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.strict-indicator :as strict] [rainbow.math.sums.indicator-zero :as iz]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(defn orders [F G n] (s/all-below n #(le (at F %) (at G %))))
(defn equals [F G n] (s/all-below n #(eqv (at G %) (at F %))))
(defn no-strict-gain [F G n] (f/arrow (orders F G n) (equals F G n)))
(defn gains [F G] (let [i (gensym "objective")] (f/lam [[i nat]] (a/sub (at G i) (at F i)))))
(defn count-losses [F G n] (sum (iz/indicators F G) n))
(defn capped-count [F G n] (cea/award b/one (count-losses F G n)))
(defn masked-gain [F G n] (mul (a/sub b/one (capped-count F G n)) (sum (gains F G) n)))
(defn nonnegative-indicators [F G n]
  (let [i (gensym "objective") hi (gensym "bound")]
    (f/lam [[i nat] [hi (s/below i n)]] (call 'signed/strict-comparison-indicator-nonnegative (at F i) (at G i)))))
(def below-one-spec
  (let [F 'F G 'G n 'n I (iz/indicators F G) total (sum I n) i 'objective x (at F i) y (at G i)
        goal (le x y)]
    (s/spec 'signed/strict-count-below-one-implies-orders
      [[F family] [G family] [n nat] ['below-one (strict/strict b/one total)]] (orders F G n)
      (f/lam [[i nat] ['bound (s/below i n)]]
        (#'cea/by-bit (cea/dec x y) (constantly goal)
          (fn [decision]
            (let [one (call 'signed/not-at-most-implies-strict-comparison-indicator x y
                        (call 'signed/decide-at-most-false-sound x y decision))
                  lower (call 'signed/term-below-sum I n (nonnegative-indicators F G n) i 'bound)]
              (call 'proposition/explode goal (at 'below-one
                (s/le-transport (at I i) b/one total total one (refl total) lower)))))
          (fn [decision] (call 'signed/decide-at-most-true-sound x y decision)) 'decision)))))
(defn count-zero [F G n order-proof]
  (call 'signed/at-most-antisymmetric (count-losses F G n) s/zero
    (call 'signed/orders-imply-zero-strict-indicator-sum F G n order-proof)
    (call 'signed/expr-sum-value-nonnegative (iz/indicators F G) n (nonnegative-indicators F G n))))
(def capped-zero-spec
  (let [count 'count goal (eqv (cea/award b/one count) s/zero)]
    (s/spec 'signed/capped-zero-count-is-zero [[count signed] ['zero (eqv count s/zero)]] goal
      (#'cea/by-bit (cea/dec b/one count) #(eqv (cea/mn b/one count %) s/zero)
        (fn [_] 'zero)
        (fn [decision]
          (call 'proposition/explode (eqv b/one s/zero)
            (call 'signed/one-not-at-most-zero
              (s/le-transport b/one b/one count s/zero (refl b/one) 'zero
                (call 'signed/decide-at-most-true-sound b/one count decision))))) 'decision))))
(def forward-spec
  (let [F 'F G 'G n 'n D (gains F G) gain (sum D n) cap (capped-count F G n) mask (a/sub b/one cap)
        capzero (call 'signed/capped-zero-count-is-zero (count-losses F G n) (count-zero F G n 'orders))
        maskone (s/trans mask (a/sub b/one s/zero) b/one
                  (s/add-cong b/one b/one (a/neg cap) (a/neg s/zero) (refl b/one) (a/neg-cong cap s/zero capzero))
                  (a/ring-eq (a/sub b/one s/zero) b/one))
        zero-gain (s/le-transport (mul mask gain) gain s/zero s/zero
                    (s/trans (mul mask gain) (mul b/one gain) gain (a/mul-cong mask b/one gain gain maskone (refl gain))
                      (call 'signed/multiply-one-left gain)) (refl s/zero) 'penalty)
        nonnegative (f/lam [['i nat] ['hi (s/below 'i n)]]
                      (call 'signed/order-implies-nonnegative-difference (at F 'i) (at G 'i) (at 'orders 'i 'hi)))]
    (s/spec 'signed/pareto-mask-implies-no-strict-gain
      [[F family] [G family] [n nat] ['penalty (le (masked-gain F G n) s/zero)]] (no-strict-gain F G n)
      (f/lam [['orders (orders F G n)] ['i nat] ['hi (s/below 'i n)]]
        (call 'signed/at-most-antisymmetric (at G 'i) (at F 'i)
          (call 'signed/nonpositive-difference-implies-at-most (at G 'i) (at F 'i)
            (a/eq-le (at D 'i) s/zero (call 'signed/nonnegative-nonpositive-sum-term-zero D n nonnegative zero-gain 'i 'hi)))
          (at 'orders 'i 'hi))))))
(def backward-spec
  (let [F 'F G 'G n 'n D (gains F G) total (count-losses F G n) gain (sum D n) Z (f/lam [['ignored nat]] s/zero)
        eqzero (fn [order-proof]
                 (s/trans gain (sum Z n) s/zero
                   (a/sum-cong D Z n 'i
                     (fn [i hi]
                       (s/trans (a/sub (at G i) (at F i)) (a/sub (at F i) (at F i)) s/zero
                         (s/add-cong (at G i) (at F i) (a/neg (at F i)) (a/neg (at F i))
                           (at 'no-gain order-proof i hi) (refl (a/neg (at F i))))
                         (a/ring-eq (a/sub (at F i) (at F i)) s/zero))))
                   (call 'signed/expr-sum-value-zero n)))]
    (s/spec 'signed/no-strict-gain-implies-pareto-mask [[F family] [G family] [n nat] ['no-gain (no-strict-gain F G n)]]
      (le (masked-gain F G n) s/zero)
      (#'cea/by-bit (cea/dec b/one total) #(le (mul (a/sub b/one (cea/mn b/one total %)) gain) s/zero)
        (fn [decision]
          (let [zero (eqzero (call 'signed/strict-count-below-one-implies-orders F G n
                              (call 'signed/decide-at-most-false-sound b/one total decision)))
                mask (a/sub b/one total)]
            (a/eq-le (mul mask gain) s/zero
              (s/trans (mul mask gain) (mul mask s/zero) s/zero (a/mul-cong mask mask gain s/zero (refl mask) zero)
                (call 'signed/multiply-zero-right mask)))))
        (fn [_] (a/eq-le (mul (a/sub b/one b/one) gain) s/zero (a/ring-eq (mul (a/sub b/one b/one) gain) s/zero))) 'decision))))
(def theorem-specs [below-one-spec capped-zero-spec forward-spec backward-spec])
(def deps '[rainbow.math.sums.indicator-zero rainbow.math.sums.zero-violations rainbow.math.sums.nonblocking rainbow.math.rational.signed.one-hot-unique])
(defn install [env] (support/extend-with env :expr-sum-pareto-mask theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.pareto-mask))
