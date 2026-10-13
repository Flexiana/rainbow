(ns rainbow.algorithms.proofs.ahof.stieltjes
  "Stieltjes three-term recurrence for orthogonal polynomials (Kochenderfer
  Optimization O21.3), a signed-cluster algorithm deferred in August until
  the signed layer landed.

  The orthogonal-polynomial recurrence evaluates
  p_n(x) = (x - alpha) * p_{n-1}(x) - beta * p_{n-2}(x). As a higher-order
  composition of signed multiply and subtract:
  `optimization/stieltjes-step x alpha beta previous second =
   signed/subtract (signed/multiply (signed/subtract x alpha) previous)
                   (signed/multiply beta second)`.
  The worked theorem proves one step for x=5, alpha=2, beta=1,
  p1=p2=1 -> (5-2)*1 - 1*1 = 2, by signed cross-product reflexivity.
  Chains signed-multiply; native and axiom-free on D63. A proved native
  module; formal ledger crediting is the separate catalog follow-up."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.map-sum-algebra :as signed-algebra]
            [rainbow.math.rational.signed.multiply :as signed-multiply]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.linear.vector.dot-subtract :as subtract-respects]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- numeral [n]
  (loop [remaining (long n) term (function/const* 'data/zero [])]
    (if (zero? remaining)
      term
      (recur (dec remaining) (app (function/const* 'data/succ []) term)))))
(defn- nnrat-of [n]
  (app (function/const* 'nnrat/make []) (numeral n)
       (function/const* 'data/zero [])))
(defn- from-nnrat [v] (app (function/const* 'signed/from-nnrat []) v))
(defn- signed-multiply [a b] (app (function/const* 'signed/multiply []) a b))
(defn- signed-subtract [a b] (app (function/const* 'signed/subtract []) a b))
(defn- signed-equivalent [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- signed-positive [v] (app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (app (function/const* 'signed/negative []) v))
(defn- nnrat-add [a b] (app (function/const* 'nnrat/add []) a b))
(defn- numerator [v] (app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [a b] (app (function/const* 'nat/multiply []) a b))

(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (app (function/const* 'equality/reflexive [type-level])
         nat (multiply-nat (numerator lhs) (denominator rhs)))))

(def stieltjes-step-spec
  {:name 'optimization/stieltjes-step :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed signed signed signed)
   :value (function/lam
           [['x signed] ['alpha signed] ['beta signed]
            ['previous signed] ['second signed]]
           (signed-subtract
            (signed-multiply (signed-subtract 'x 'alpha) 'previous)
            (signed-multiply 'beta 'second)))})

(defn- step [x alpha beta previous second]
  (app (function/const* 'optimization/stieltjes-step [])
       x alpha beta previous second))

(def stieltjes-step-worked-spec
  "One recurrence step for x=5, alpha=2, beta=1, p1=p2=1 yields 2."
  {:name 'optimization/stieltjes-step-worked :universes []
   :type (let [one (from-nnrat (nnrat-of 1))]
           (signed-equivalent
            (step (from-nnrat (nnrat-of 5)) (from-nnrat (nnrat-of 2))
                  one one one)
            (from-nnrat (nnrat-of 2))))
   :value (let [one (from-nnrat (nnrat-of 1))]
            (signed-equivalent-cross
             (step (from-nnrat (nnrat-of 5)) (from-nnrat (nnrat-of 2))
                   one one one)
             (from-nnrat (nnrat-of 2))))})

(def signed-zero (function/const* 'signed/zero []))
(defn- signed-equivalent-tr [a b c p q]
  (app (function/const* 'signed/equivalent-transitive []) a b c p q))

(def stieltjes-step-preserves-zero-spec
  "The UNIVERSAL linearity witness: the recurrence is a linear operator,
  so it fixes the zero polynomial -- stieltjes-step x alpha beta 0 0 ~ 0
  for all coefficients. Both products vanish (multiply by zero), and the
  difference of two zeros is zero. Upgrades the worked instance to an
  all-coefficients guarantee."
  {:name 'optimization/stieltjes-step-preserves-zero :universes []
   :type (function/forall
          [['x signed] ['alpha signed] ['beta signed]]
          (signed-equivalent
           (step 'x 'alpha 'beta signed-zero signed-zero) signed-zero))
   :value
   (function/lam
    [['x signed] ['alpha signed] ['beta signed]]
    (let [x-alpha (signed-subtract 'x 'alpha)
          first-term (signed-multiply x-alpha signed-zero)
          second-term (signed-multiply 'beta signed-zero)
          first-zero (app (function/const* 'signed/multiply-zero-right []) x-alpha)
          second-zero (app (function/const* 'signed/multiply-zero-right []) 'beta)
          diff-respects (app (function/const* 'signed/subtract-respects-equivalence [])
                             first-term signed-zero second-term signed-zero
                             first-zero second-zero)
          self-zero (app (function/const* 'signed/subtract-self-equivalent-zero [])
                         signed-zero)]
      (signed-equivalent-tr
       (signed-subtract first-term second-term)
       (signed-subtract signed-zero signed-zero)
       signed-zero
       diff-respects self-zero)))})

(def definition-specs [stieltjes-step-spec])
(def theorem-specs [stieltjes-step-worked-spec
                    stieltjes-step-preserves-zero-spec])

(defn- guard [env alias extend]
  (if (environment/resolve-id env alias) env (extend env)))

(defn extend-environment [env]
  (-> env
      signed-multiply/extend-environment
      (guard 'signed/multiply-zero-right multiply-ring/extend-environment)
      (guard 'signed/subtract-respects-equivalence
             subtract-respects/extend-environment)
      (guard 'signed/subtract-self-equivalent-zero unit-laws/extend-environment)
      (guard 'signed/equivalent-transitive signed-algebra/extend-environment)
      (support/extend-with :ahof-stieltjes
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
