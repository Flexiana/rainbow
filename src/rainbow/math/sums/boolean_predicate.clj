(ns rainbow.math.sums.boolean-predicate
  "The converse of the existing zero/one polynomial lemma, for predicate adapters."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.logic.proposition :as prop]
            [rainbow.math.sums.value-algebra :as s :refer [signed call eqv mul refl]]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))
(defn binary [x] (prop/disjunction (eqv x s/zero) (eqv x b/one)))
(defn polynomial [x] (mul x (a/sub b/one x)))
(def polynomial-spec
  (let [x 'x P (eqv x s/zero) Q (eqv x b/one) goal (eqv (polynomial x) s/zero)
        branch (fn [v]
                 (f/lam [['value (eqv x v)]]
                   (s/trans (polynomial x) (polynomial v) s/zero
                     (a/mul-cong x v (a/sub b/one x) (a/sub b/one v) 'value
                       (s/add-cong b/one b/one (a/neg x) (a/neg v) (refl b/one)
                         (a/neg-cong x v 'value)))
                     (a/ring-eq (polynomial v) s/zero))))]
    (s/spec 'signed/boolean-cases-implies-polynomial
      [[x signed] ['binary (binary x)]] goal
      (a/cases P Q goal 'binary (branch s/zero) (branch b/one)))))
(def theorem-specs [polynomial-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.multiply-nonzero
            rainbow.math.rational.signed.lp-objective-negate])
(defn install [env]
  (-> env (support/extend-with-shared :boolean-predicate-prerequisites [a/bit-split-spec])
    (support/extend-with :expr-sum-boolean-predicate theorem-specs)))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.boolean-predicate))
