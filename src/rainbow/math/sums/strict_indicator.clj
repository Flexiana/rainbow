(ns rainbow.math.sums.strict-indicator
  "A strict comparison indicator is one exactly when the reverse weak inequality is false."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def U [:succ [:zero]])
(def bool (f/const* 'data/Bool []))
(def true-bit (f/const* 'data/true []))
(defn selected [bit] (f/app (f/const* 'data/Bool.rec [U]) (f/lam [['ignored bool]] signed) b/one s/zero bit))
(defn indicator [x y] (selected (call 'signed/decide-at-most x y)))
(defn strict [x y] (call 'proposition/negation (le x y)))
(def nonnegative-spec
  (s/spec 'signed/strict-comparison-indicator-nonnegative [['x signed] ['y signed]]
    (le s/zero (indicator 'x 'y))
    (f/app (f/const* 'data/Bool.rec [[:zero]])
      (f/lam [['bit bool]] (le s/zero (selected 'bit)))
      (call 'signed/less-than-implies-at-most s/zero b/one (f/const* 'signed/zero-less-than-one []))
      (call 'signed/at-most-reflexive s/zero) (call 'signed/decide-at-most 'x 'y))))
(def forward-spec
  (let [D (call 'signed/decide-at-most 'x 'y)]
    (s/spec 'signed/strict-comparison-indicator-implies-not-at-most
      [['x signed] ['y signed] ['indicator (le b/one (indicator 'x 'y))]] (strict 'x 'y)
      (f/lam [['contrary (le 'x 'y)]]
        (call 'signed/one-not-at-most-zero
          (f/app (f/const* 'equality/substitution [U]) bool D true-bit
            (call 'signed/decide-at-most-true-complete 'x 'y 'contrary)
            (f/lam [['bit bool]] (le b/one (selected 'bit))) 'indicator))))))
(def backward-spec
  (s/spec 'signed/not-at-most-implies-strict-comparison-indicator
    [['x signed] ['y signed] ['strict (strict 'x 'y)]] (eqv (indicator 'x 'y) b/one)
    (#'cea/by-bit (call 'signed/decide-at-most 'x 'y) #(eqv (selected %) b/one)
      (fn [_] (refl b/one))
      (fn [h] (call 'proposition/explode (eqv s/zero b/one)
                (f/app 'strict (call 'signed/decide-at-most-true-sound 'x 'y h)))) 'decision)))
(def theorem-specs [nonnegative-spec forward-spec backward-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.strict-order])
(defn install [env] (support/extend-with env :expr-sum-strict-indicator theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.strict-indicator))
