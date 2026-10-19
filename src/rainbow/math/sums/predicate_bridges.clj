(ns rainbow.math.sums.predicate-bridges
  "Reusable bridges from checker indicators and squared norms to mathematical predicates."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym]]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.abc-class :as indicator]
            [rainbow.math.lemmas.hhi-bounds :as hhi]
            [rainbow.math.lemmas.indep-set-dual :as order]
            [rainbow.math.lemmas.mctrans-step :as squares]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))
(def U [:succ [:zero]])
(def bool (f/const* 'data/Bool []))
(defn negation [p] (call 'proposition/negation p))
(defn lt [x y] (call 'signed/less-than x y))
(defn all-zero [v n] (s/all-below n #(eqv (at v %) s/zero)))
(defn nonzero [v n] (negation (all-zero v n)))
(defn square-family [v] (let [i (gensym "square")] (f/lam [[i nat]] (mul (at v i) (at v i)))))
(defn normsq [v n] (sum (square-family v) n))
(def positive-indicator-spec
  (let [x 'x D (call 'signed/decide-at-most x s/zero)
        select #(f/app (f/const* 'data/Bool.rec [U]) (f/lam [['ignored bool]] signed) b/one s/zero %)
        lower (call 'signed/less-than-implies-at-most s/zero x 'positive)
        different (call 'proposition/right (le s/zero x) (negation (eqv s/zero x)) 'positive)
        not-le (f/lam [['reverse (le x s/zero)]]
                 (at different (call 'signed/at-most-antisymmetric s/zero x lower 'reverse)))
        decided (call 'signed/decide-at-most-false-complete x s/zero not-le)]
    (s/spec 'signed/positive-implies-indicator-one [['x signed] ['positive (lt s/zero x)]]
      (le b/one (indicator/strict-ind s/zero x))
      (f/app (f/const* 'equality/substitution [U]) bool (f/const* 'data/false []) D
        (f/app (f/const* 'equality/symmetric [U]) bool D (f/const* 'data/false []) decided)
        (f/lam [['choice bool]] (le b/one (select 'choice)))
        (call 'signed/at-most-reflexive b/one)))))
(def positive-norm-spec
  (let [v 'v n 'n Q (square-family v) S (sum Q n) Z (f/lam [['zero-index nat]] s/zero)
        zero (s/trans S (sum Z n) s/zero
               (a/sum-cong Q Z n 'entry
                 (fn [i hi] (s/trans (mul (at v i) (at v i)) (mul s/zero (at v i)) s/zero
                              (a/mul-cong (at v i) s/zero (at v i) (at v i) (at 'all-zero i hi) (refl (at v i)))
                              (call 'signed/multiply-zero-left (at v i)))))
               (call 'signed/expr-sum-value-zero n))
        neq (call 'proposition/right (le s/zero S) (negation (eqv s/zero S)) 'positive)]
    (s/spec 'signed/positive-square-sum-implies-nonzero
      [[v family] [n nat] ['positive (lt s/zero S)]] (nonzero v n)
      (f/lam [['all-zero (all-zero v n)]] (at neq (sym S s/zero zero))))))
(def nonzero-norm-spec
  (let [v 'v n 'n Q (square-family v) S (sum Q n)
        nn (call 'signed/expr-sum-value-nonnegative Q n
             (f/lam [['entry nat] ['bound (s/below 'entry n)]]
               (call 'signed/zero-at-most-of-nonnegative (mul (at v 'entry) (at v 'entry))
                 (call 'signed/square-nonnegative (at v 'entry)))))]
    (s/spec 'signed/nonzero-implies-positive-square-sum
      [[v family] [n nat] ['nonzero (nonzero v n)]] (lt s/zero S)
      (call 'signed/less-than-intro s/zero S nn
        (f/lam [['zero (eqv s/zero S)]]
          (at 'nonzero (call 'signed/square-sum-zero-terms v n (a/eq-le S s/zero (sym s/zero S 'zero)))))))))
(def theorem-specs [positive-indicator-spec positive-norm-spec nonzero-norm-spec])
(def borrowed-specs [order/total-spec hhi/positive-spec squares/square-sum-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.sums.nonneg-zero
            rainbow.math.linear.vector.norm-nonnegative rainbow.math.rational.signed.square-zero
            rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.decide-completeness])
(defn install [env]
  (-> env (support/extend-with-shared :predicate-bridge-prerequisites borrowed-specs)
    (support/extend-with :expr-sum-predicate-bridges theorem-specs)))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.predicate-bridges))
