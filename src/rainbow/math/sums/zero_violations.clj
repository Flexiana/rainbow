(ns rainbow.math.sums.zero-violations
  "Zero positive-part penalties mean no violated inequality; a minimum encodes disjunction."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.binary-conflicts :as binary]
            [rainbow.math.lemmas.ufl-gap :as ufl]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def pp ufl/positive-part)
(def minimum cea/award)
(def zero-of-nonpositive-spec
  (s/spec 'signed/positive-part-zero-of-nonpositive [['x signed] ['nonpositive (le 'x s/zero)]]
    (eqv (pp 'x) s/zero)
    (#'ufl/bool-split 'x (fn [bit] (eqv (#'ufl/selected 'x bit) s/zero))
      (fn [_] (refl s/zero))
      (fn [nonnegative] (call 'signed/at-most-antisymmetric 'x s/zero 'nonpositive nonnegative)))))
(def nonpositive-of-zero-spec
  (s/spec 'signed/nonpositive-of-positive-part-zero [['x signed] ['zero (eqv (pp 'x) s/zero)]]
    (le 'x s/zero)
    (a/le-trans 'x (pp 'x) s/zero (call 'signed/positive-part-upper 'x) (a/eq-le (pp 'x) s/zero 'zero))))
(def minimum-nonpositive-spec
  (let [x 'x y 'y P (le x s/zero) Q (le y s/zero) goal (a/disj P Q)]
    (s/spec 'signed/nonpositive-minimum-implies-disjunction [[x signed] [y signed] ['nonpositive (le (minimum x y) s/zero)]] goal
      (at (#'cea/by-bit (cea/dec x y)
        (fn [bit] (f/arrow (le (cea/mn x y bit) s/zero) goal))
        (fn [_] (f/lam [['hyp Q]] (call 'proposition/right-disjunct P Q 'hyp)))
        (fn [_] (f/lam [['hyp P]] (call 'proposition/left-disjunct P Q 'hyp))) 'decision) 'nonpositive))))
(def disjunction-minimum-spec
  (let [x 'x y 'y P (le x s/zero) Q (le y s/zero)]
    (s/spec 'signed/disjunction-implies-nonpositive-minimum [[x signed] [y signed] ['either (a/disj P Q)]]
      (le (minimum x y) s/zero)
      (#'cea/by-bit (cea/dec x y) #(le (cea/mn x y %) s/zero)
        (fn [h] (a/cases P Q (le y s/zero) 'either
                  (f/lam [['hx P]] (a/le-trans y x s/zero (call 'signed/decide-at-most-false-reverse x y h) 'hx))
                  (f/lam [['hy Q]] 'hy)))
        (fn [h] (a/cases P Q (le x s/zero) 'either
                  (f/lam [['hx P]] 'hx)
                  (f/lam [['hy Q]] (a/le-trans x y s/zero (call 'signed/decide-at-most-true-sound x y h) 'hy)))) 'decision))))
(def subtract-to-order-spec
  (s/spec 'signed/nonpositive-difference-implies-at-most
    [['x signed] ['y signed] ['difference (le (a/sub 'x 'y) s/zero)]] (le 'x 'y)
    (s/le-transport (s/add (a/sub 'x 'y) 'y) 'x (s/add s/zero 'y) 'y
      (a/ring-eq (s/add (a/sub 'x 'y) 'y) 'x) (a/ring-eq (s/add s/zero 'y) 'y)
      (call 'signed/add-right-monotone (a/sub 'x 'y) s/zero 'y 'difference))))
(def order-to-subtract-spec
  (s/spec 'signed/at-most-implies-nonpositive-difference
    [['x signed] ['y signed] ['ordered (le 'x 'y)]] (le (a/sub 'x 'y) s/zero)
    (s/le-transport (a/sub 'x 'y) (a/sub 'x 'y) (a/sub 'y 'y) s/zero
      (refl (a/sub 'x 'y)) (a/ring-eq (a/sub 'y 'y) s/zero)
      (call 'signed/add-right-monotone 'x 'y (call 'signed/negate 'y) 'ordered))))
(defn weighted [W V] (let [i (gensym "entry")] (f/lam [[i nat]] (mul (at W i) (pp (at V i))))))
(defn bits [W n] (s/all-below n #(call 'proposition/disjunction (eqv (at W %) s/zero) (eqv (at W %) b/one))))
(defn implications [W V n]
  (let [i (gensym "entry") bound (gensym "bound") selected (gensym "selected")]
    (f/forall [[i nat] [bound (s/below i n)] [selected (eqv (at W i) b/one)]] (le (at V i) s/zero))))
(def sum-to-implications-spec
  (let [W 'W V 'V n 'n i 'i value (at V i) w (at W i) pv (pp value)
        F (weighted W V)
        nn (f/lam [['j nat] ['hj (s/below 'j n)]]
             (binary/nnprod (at W 'j) (pp (at V 'j))
               (call 'signed/boolean-cases-nonnegative (at W 'j) (at 'binary 'j 'hj))
               (call 'signed/positive-part-nonneg (at V 'j))))
        pzero (a/chain pv
                [(mul b/one pv) (s/sym (mul b/one pv) pv (call 'signed/multiply-one-left pv))]
                [(mul w pv) (a/mul-cong b/one w pv pv (s/sym w b/one 'selected) (refl pv))]
                [s/zero (call 'signed/nonnegative-nonpositive-sum-term-zero F n nn 'sum i 'bound)])]
    (s/spec 'signed/zero-penalty-sum-implies-constraints
      [[W family] [V family] [n nat] ['binary (bits W n)] ['sum (le (sum F n) s/zero)]]
      (implications W V n)
      (f/lam [[i nat] ['bound (s/below i n)] ['selected (eqv w b/one)]]
        (call 'signed/nonpositive-of-positive-part-zero value pzero)))))
(def implications-to-sum-spec
  (let [W 'W V 'V n 'n F (weighted W V) Z (f/lam [['unused nat]] s/zero)]
    (s/spec 'signed/constraints-imply-zero-penalty-sum
      [[W family] [V family] [n nat] ['binary (bits W n)] ['constraints (implications W V n)]]
      (le (sum F n) s/zero)
      (a/eq-le (sum F n) s/zero
        (s/trans (sum F n) (sum Z n) s/zero
          (a/sum-cong F Z n 'entry
            (fn [i hi]
              (let [w (at W i) v (at V i) pv (pp v) goal (eqv (mul w pv) s/zero)
                    P (eqv w s/zero) Q (eqv w b/one)]
                (a/cases P Q goal (at 'binary i hi)
                  (f/lam [['zero P]] (s/trans (mul w pv) (mul s/zero pv) s/zero
                                      (a/mul-cong w s/zero pv pv 'zero (refl pv)) (call 'signed/multiply-zero-left pv)))
                  (f/lam [['one Q]] (s/trans (mul w pv) (mul w s/zero) s/zero
                                     (a/mul-cong w w pv s/zero (refl w)
                                       (call 'signed/positive-part-zero-of-nonpositive v (at 'constraints i hi 'one)))
                                     (call 'signed/multiply-zero-right w)))))))
          (call 'signed/expr-sum-value-zero n))))))
(def theorem-specs [zero-of-nonpositive-spec nonpositive-of-zero-spec minimum-nonpositive-spec disjunction-minimum-spec
                    subtract-to-order-spec order-to-subtract-spec sum-to-implications-spec implications-to-sum-spec])
(def deps '[rainbow.math.sums.binary-conflicts rainbow.math.rational.signed.decide-order])
(defn install [env]
  (-> env (support/extend-with-shared :zero-violations-prerequisites [ufl/positive-part-upper-spec ufl/positive-part-nonneg-spec])
      (support/extend-with :expr-sum-zero-violations theorem-specs)))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.zero-violations))
