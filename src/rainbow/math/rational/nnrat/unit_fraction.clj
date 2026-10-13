(ns rainbow.math.rational.nnrat.unit-fraction
  "Explicit positive unit fractions and their proper complements.
  Kernel-checked and axiom-free on D63. All identities use
  rational equivalence, not structural equality of raw representatives."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.semiring :as semiring]
            [rainbow.math.rational.nnrat.positive :as positive]))

(def type-level [:succ [:zero]])
(def nat (f/const* 'data/Nat []))
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(def nat-zero (f/const* 'data/zero []))
(def nat-one (app 'data/succ nat-zero))
(def one (f/const* 'nnrat/one []))
(defn unit-fraction [dp] (app 'nnrat/make nat-one dp))
(defn proper-complement [dp] (app 'nnrat/make dp dp))
(defn- nadd [a b] (app 'algebra/nat-add a b))
(defn- nmul [a b] (app 'nat/multiply a b))
(defn- nat-sym [a b p]
  (f/app (f/const* 'equality/symmetric [type-level]) nat a b p))
(defn- nat-trans [a b c p q]
  (f/app (f/const* 'equality/transitive [type-level]) nat a b c p q))

(def unit-fraction-at-most-positive-spec
  (let [dp (app 'nnrat/denominator-predecessor 'value)
        epsilon (unit-fraction dp)
        bindings [['value nnrat] ['positive (app 'nnrat/positive 'value)]]]
    {:name 'nnrat/unit-fraction-at-most-positive :universes []
     :type (f/forall bindings (app 'nnrat/at-most epsilon 'value))
     :value (f/lam bindings
              (app 'nnrat/at-most-from-cross epsilon 'value
                (app 'nat/multiply-right-monotone (app 'nnrat/denominator 'value)
                     nat-one (app 'nnrat/numerator 'value) 'positive)))}))

(def unit-fraction-positive-spec
  {:name 'nnrat/unit-fraction-positive :universes []
   :type (f/forall [['dp nat]] (app 'nnrat/positive (unit-fraction 'dp)))
   :value (f/lam [['dp nat]] (f/const* 'nnrat/one-positive []))})

(def unit-fraction-complement-spec
  (let [epsilon (unit-fraction 'dp) rho (proper-complement 'dp)
        sum (app 'nnrat/add rho epsilon)
        d (app 'data/succ 'dp) a (nmul 'dp d) b (nmul nat-one d)
        numerator (nadd a b) left (nmul numerator nat-one)
        simplified (nadd a d) square (nmul d d)
        denominator (app 'nnrat/denominator sum) right (nmul nat-one denominator)
        simplify-one
        (f/app (f/const* 'equality/congruent-function [type-level type-level])
          nat nat (f/lam [['x nat]] (nadd a 'x)) b d
          (app 'algebra/nat-add-zero-right d))]
    {:name 'nnrat/unit-fraction-plus-complement :universes []
     :type (f/forall [['dp nat]] (app 'nnrat/equivalent sum one))
     :value
     (f/lam [['dp nat]]
       (nat-trans left numerator right (app 'nat/multiply-one-right numerator)
         (nat-trans numerator simplified right simplify-one
           (nat-trans simplified square right (app 'nat/add-commutative a d)
             (nat-trans square denominator right
               (nat-sym denominator square (app 'nnrat/denominator-combine 'dp 'dp))
               (nat-sym right denominator (app 'algebra/nat-add-zero-right denominator)))))))}))

(def unit-fraction-complement-proper-spec
  (let [rho (proper-complement 'dp)]
    {:name 'nnrat/unit-fraction-complement-proper :universes []
     :type (f/forall [['dp nat]]
             (app 'nat/at-most (app 'nnrat/numerator rho)
                              (app 'nnrat/denominator-predecessor rho)))
     :value (f/lam [['dp nat]] (app 'nat/at-most-reflexive 'dp))}))

(def theorem-specs [unit-fraction-at-most-positive-spec unit-fraction-positive-spec
                    unit-fraction-complement-spec unit-fraction-complement-proper-spec])
(defn extend-environment [env]
  (let [env (positive/extend-environment env)
        env (if (environment/resolve-id env 'nat/multiply-one-right) env
                (support/extend-with env :nnrat-unit-fraction-support [semiring/multiply-one-right-spec]))]
    (support/extend-with env :nnrat-unit-fraction theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
