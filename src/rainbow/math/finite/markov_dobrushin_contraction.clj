(ns rainbow.math.finite.markov-dobrushin-contraction
  "Inhabitant of the frozen finite Dobrushin contraction predicate.
  Split the residual total by its rational numerator. The zero case uses
  mass preservation; the positive case uses the proved product coupling.
  No contraction premise, positive-mass assumption, or new axiom is added."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-residual-coupling :as residual]
            [rainbow.math.finite.markov-coupling-coefficient :as positive]
            [rainbow.math.finite.markov-dobrushin-statement :as statement]
            [rainbow.math.finite.markov-kernel-composition :as composition]))

(def U [:param 'u])
(def T [:succ [:zero]])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat residual/nnrat)
(def nat residual/nat)
(def zero (c 'nnrat/zero))
(def nzero (c 'data/zero))
(defn- eqv [a b] (app 'nnrat/equivalent a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- add [a b] (app 'nnrat/add a b))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- refl [a] (app 'nnrat/equivalent-reflexive a))
(defn- sym [a b p] (app 'nnrat/equivalent-symmetric a b p))
(defn- trans [a b c p q] (app 'nnrat/equivalent-transitive a b c p q))
(defn- total [mass] (poly 'probability/nnrat-total-mass 'S 'states mass))
(defn- l1 [a b] (poly 'markov/nnrat-total-variation 'S 'states a b))
(defn- step [mass] (poly 'markov/nnrat-kernel-step 'S 'states 'kernel mass))
(defn- normalized [] (poly 'markov/nnrat-kernel-rows-normalized 'S 'states 'kernel))
(defn- conclusion [] (le (l1 (step 'left) (step 'right)) (mul 'rho (l1 'left 'right))))

(def zero-residual-contraction-spec
  (let [p (residual/residual-mapping :left) q (residual/residual-mapping :right)
        bindings (into residual/base-binders
                       [['kernel (f/arrow 'S 'S nnrat)] ['normalized (normalized)]
                        ['same-total (eqv (total 'left) (total 'right))]
                        ['zero-residual-total (eqv (total p) zero)] ['rho nnrat]])
        q-zero (trans (total q) (total p) zero
                 (sym (total p) (total q)
                   (poly 'markov/nnrat-residual-totals-equal 'S 'states 'left 'right 'same-total))
                 'zero-residual-total)
        step-zero (fn [mass proof]
                    (trans (total (step mass)) (total mass) zero
                      (poly 'markov/nnrat-kernel-step-preserves-total-mass-equivalence
                            'S 'states 'kernel mass 'normalized) proof))
        mass-sum (add (total (step p)) (total (step q)))
        sum-zero (trans mass-sum (add zero zero) zero
                   (app 'nnrat/add-respects-equivalence
                        (total (step p)) zero (total (step q)) zero
                        (step-zero p 'zero-residual-total) (step-zero q q-zero))
                   (app 'nnrat/add-zero-right zero))
        lhs (l1 (step 'left) (step 'right)) middle (l1 (step p) (step q))
        rhs (mul 'rho (l1 'left 'right))]
    {:name 'markov/nnrat-kernel-step-zero-residual-contraction :universes ['u]
     :type (f/forall bindings (conclusion))
     :value
     (f/lam bindings
       (app 'nnrat/at-most-transitive lhs zero rhs
         (app 'nnrat/at-most-respects-equivalence lhs middle zero mass-sum
           (poly 'markov/nnrat-kernel-step-total-variation-residual 'S 'states 'kernel 'left 'right)
           (sym mass-sum zero sum-zero)
           (poly 'markov/nnrat-total-variation-at-most-mass-sum 'S 'states (step p) (step q)))
         (app 'nnrat/zero-at-most rhs)))}))

(defn- residual-case [candidate]
  (f/arrow (eqv (total (residual/residual-mapping :left)) candidate) (conclusion)))

(def contraction-spec
  (let [bindings (into statement/parameters
                       [['normalized (normalized)]
                        (second positive/coefficient-binders)
                        ['left (f/arrow 'S nnrat)] ['right (f/arrow 'S nnrat)]
                        ['equal-total-mass (eqv (total 'left) (total 'right))]])
        p (total (residual/residual-mapping :left))
        made (fn [n] (app 'nnrat/make n 'denominator-predecessor))
        nat-motive (f/lam [['n nat]] (residual-case (made 'n)))]
    {:name 'markov/nnrat-dobrushin-contraction :universes ['u]
     :type (f/forall statement/parameters
             (poly 'markov/nnrat-dobrushin-contraction-estimate 'S 'states 'kernel 'rho))
     :value
     (f/lam bindings
       (f/app
         (f/app (f/const* 'data/Product.rec [T T [:zero]]) nat nat
           (f/lam [['candidate nnrat]] (residual-case 'candidate))
           (f/lam [['numerator nat] ['denominator-predecessor nat]]
             (f/app (f/const* 'data/Nat.rec [[:zero]]) nat-motive
               (f/lam [['residual-total (eqv p (made nzero))]]
                 (poly 'markov/nnrat-kernel-step-zero-residual-contraction
                       'S 'states 'left 'right 'kernel 'normalized 'equal-total-mass
                       (trans p (made nzero) zero 'residual-total
                         (f/app (f/const* 'equality/reflexive [T]) nat nzero)) 'rho))
               (f/lam [['ap nat] ['unused-induction-hypothesis (f/app nat-motive 'ap)]
                       ['residual-total (eqv p (made (app 'data/succ 'ap)))]]
                 (poly 'markov/nnrat-kernel-step-positive-residual-contraction
                       'S 'states 'left 'right 'kernel 'ap 'denominator-predecessor
                       'equal-total-mass 'residual-total 'rho 'coefficient-bound))
               'numerator)) p)
         (refl p)))}))

(def theorem-specs [zero-residual-contraction-spec contraction-spec])
(defn extend-environment [env]
  (-> env positive/extend-environment statement/extend-environment
      ((fn [e] (if (environment/resolve-id e 'markov/nnrat-kernel-step-preserves-total-mass-equivalence) e
                 (support/add-spec e :finite-markov-dobrushin-contraction-support
                                   composition/kernel-step-preserves-total-mass-spec))))
      (support/extend-with :finite-markov-dobrushin-contraction theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
