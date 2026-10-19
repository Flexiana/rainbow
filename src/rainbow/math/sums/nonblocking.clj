(ns rainbow.math.sums.nonblocking
  "An encoded maximum is nonnegative exactly when at least one preference gap is."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call at le eqv refl]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(defn max-bit [x y bit] (cea/mn y x bit))
(defn maximum [x y] (max-bit x y (cea/dec x y)))
(defn preferences [own candidate other-own other-candidate]
  (a/disj (le own candidate) (le other-own other-candidate)))
(defn encoded [own candidate other-own other-candidate]
  (le s/zero (maximum (a/sub candidate own) (a/sub other-candidate other-own))))
(def order-from-gap-spec
  (s/spec 'signed/nonnegative-difference-implies-order [['x signed] ['y signed] ['gap (le s/zero (a/sub 'y 'x))]]
    (le 'x 'y)
    (s/le-transport (s/add s/zero 'x) 'x (s/add (a/sub 'y 'x) 'x) 'y
      (a/ring-eq (s/add s/zero 'x) 'x) (a/ring-eq (s/add (a/sub 'y 'x) 'x) 'y)
      (call 'signed/add-right-monotone s/zero (a/sub 'y 'x) 'x 'gap))))
(def gap-from-order-spec
  (s/spec 'signed/order-implies-nonnegative-difference [['x signed] ['y signed] ['order (le 'x 'y)]]
    (le s/zero (a/sub 'y 'x))
    (s/le-transport (a/sub 'x 'x) s/zero (a/sub 'y 'x) (a/sub 'y 'x)
      (a/ring-eq (a/sub 'x 'x) s/zero) (refl (a/sub 'y 'x))
      (call 'signed/add-right-monotone 'x 'y (a/neg 'x) 'order))))
(def forward-spec
  (let [x 'x y 'y z 'z w 'w a (a/sub y x) b (a/sub w z) P (le x y) Q (le z w) goal (a/disj P Q)]
    (s/spec 'signed/nonnegative-maximum-gaps-implies-nonblocking
      [[x signed] [y signed] [z signed] [w signed] ['encoded (encoded x y z w)]] goal
      (at (#'cea/by-bit (cea/dec a b) #(f/arrow (le s/zero (max-bit a b %)) goal)
            (fn [_] (f/lam [['gap (le s/zero a)]]
                      (call 'proposition/left-disjunct P Q (call 'signed/nonnegative-difference-implies-order x y 'gap))))
            (fn [_] (f/lam [['gap (le s/zero b)]]
                      (call 'proposition/right-disjunct P Q (call 'signed/nonnegative-difference-implies-order z w 'gap)))) 'decision) 'encoded))))
(def backward-spec
  (let [x 'x y 'y z 'z w 'w a (a/sub y x) b (a/sub w z) P (le x y) Q (le z w)]
    (s/spec 'signed/nonblocking-implies-nonnegative-maximum-gaps
      [[x signed] [y signed] [z signed] [w signed] ['preferences (preferences x y z w)]] (encoded x y z w)
      (#'cea/by-bit (cea/dec a b) #(le s/zero (max-bit a b %))
        (fn [decision]
          (a/cases P Q (le s/zero a) 'preferences
            (f/lam [['order P]] (call 'signed/order-implies-nonnegative-difference x y 'order))
            (f/lam [['order Q]] (a/le-trans s/zero b a (call 'signed/order-implies-nonnegative-difference z w 'order)
                                  (call 'signed/decide-at-most-false-reverse a b decision)))))
        (fn [decision]
          (a/cases P Q (le s/zero b) 'preferences
            (f/lam [['order P]] (a/le-trans s/zero a b (call 'signed/order-implies-nonnegative-difference x y 'order)
                                  (call 'signed/decide-at-most-true-sound a b decision)))
            (f/lam [['order Q]] (call 'signed/order-implies-nonnegative-difference z w 'order)))) 'decision))))
(def theorem-specs [order-from-gap-spec gap-from-order-spec forward-spec backward-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.decide-order])
(defn install [env] (support/extend-with env :expr-sum-nonblocking theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.nonblocking))
