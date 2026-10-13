(ns rainbow.algorithms.proofs.ahof.weighted-estimators
  "Kochenderfer weighted-sum / additive estimators (across Optimization and Validation)
  as higher-order-function compositions, proved axiom-free, extending the 222 AHoF
  catalog:

    V7.4  multiple importance sampling : balance-weighted combination of proposals
    V11.3 integrated gradients         : path-sum attribution (completeness: sum = delta)
    O6.4  Gauss-Newton Hessian         : sum of squared Jacobian terms
    O17.6 ridge regression             : data loss + lambda * penalty
    O21.5 Bayesian Monte Carlo         : quadrature-weighted mean

  MIS reuses nnrat/wsum2 and inherits the convex bound (estimate <= max proposal when
  balance weights sum to one).  The rest are add/multiply compositions with worked
  instances.  Native and axiom-free; chains nnrat-convex (-> wsum2, minmax) on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))

(defn- wsum2 [w0 w1 v0 v1] (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(def ^:private nat (function/const* 'data/Nat []))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- equiv-cross [x lit]
  (function/app (function/const* 'equality/reflexive [type-level]) nat (nmul (num x) (den lit))))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- numeral [n] (nth (iterate succ zero-nat) n))
(defn- rational [n d-pred] (function/app (function/const* 'nnrat/make []) (numeral n) (numeral d-pred)))
(def half (rational 1 1))

;; ---- V7.4 multiple importance sampling: balance-weighted combination ---------
(def mis-combine-spec
  {:name 'est/mis-combine :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['f0 nnrat] ['f1 nnrat]]
                        (wsum2 'w0 'w1 'f0 'f1))})

;; with balance weights summing to one, the MIS estimate never exceeds the larger proposal
(def mis-within-max-spec
  {:name 'est/mis-within-max :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['f0 nnrat] ['f1 nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'est/mis-combine []) 'w0 'w1 'f0 'f1)
                                   (rmax 'f0 'f1)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['f0 nnrat] ['f1 nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'f0 'f1 'hw))})

;; ---- V11.3 integrated gradients: attribution total (completeness) ------------
(def ig-total-spec
  {:name 'xai/ig-attribution-total :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a0 nnrat] ['a1 nnrat]] (radd 'a0 'a1))})

;; completeness worked instance: per-feature attributions 1/2 + 1/2 sum to f(x)-f(base)=1
(def ig-completeness-example-spec
  {:name 'xai/ig-completeness-example :universes []
   :type (equiv (function/app (function/const* 'xai/ig-attribution-total []) half half) (rational 1 0))
   :value (equiv-cross (function/app (function/const* 'xai/ig-attribution-total []) half half) (rational 1 0))})

;; ---- O6.4 Gauss-Newton Hessian: sum of squared Jacobian terms ----------------
(def gauss-newton-hessian-spec
  {:name 'opt/gauss-newton-hessian :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['j0 nnrat] ['j1 nnrat]] (radd (rmul 'j0 'j0) (rmul 'j1 'j1)))})

;; worked: J = (1,2) -> Hessian approx 1 + 4 = 5
(def gauss-newton-example-spec
  {:name 'opt/gauss-newton-example :universes []
   :type (equiv (function/app (function/const* 'opt/gauss-newton-hessian [])
                              (rational 1 0) (rational 2 0)) (rational 5 0))
   :value (equiv-cross (function/app (function/const* 'opt/gauss-newton-hessian [])
                                     (rational 1 0) (rational 2 0)) (rational 5 0))})

;; ---- O17.6 ridge regression: data loss + lambda * penalty --------------------
(def ridge-objective-spec
  {:name 'opt/ridge-objective :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['loss nnrat] ['lambda nnrat] ['penalty nnrat]]
                        (radd 'loss (rmul 'lambda 'penalty)))})

;; worked: loss 1/2, lambda 1, penalty 1/2 -> regularized objective 1
(def ridge-example-spec
  {:name 'opt/ridge-example :universes []
   :type (equiv (function/app (function/const* 'opt/ridge-objective []) half rone half) (rational 1 0))
   :value (equiv-cross (function/app (function/const* 'opt/ridge-objective []) half rone half) (rational 1 0))})

;; ---- O21.5 Bayesian Monte Carlo: quadrature-weighted mean --------------------
(def bayesian-mc-mean-spec
  {:name 'est/bayesian-mc-mean :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['f0 nnrat] ['f1 nnrat]]
                        (wsum2 'w0 'w1 'f0 'f1))})

;; worked: equal quadrature weights over f=(1,0) -> mean 1/2
(def bayesian-mc-example-spec
  {:name 'est/bayesian-mc-example :universes []
   :type (equiv (function/app (function/const* 'est/bayesian-mc-mean []) half half rone (rational 0 0))
                (rational 1 1))
   :value (equiv-cross (function/app (function/const* 'est/bayesian-mc-mean []) half half rone (rational 0 0))
                       (rational 1 1))})

(def definition-specs
  [mis-combine-spec ig-total-spec gauss-newton-hessian-spec ridge-objective-spec
   bayesian-mc-mean-spec])
(def theorem-specs
  [mis-within-max-spec ig-completeness-example-spec gauss-newton-example-spec
   ridge-example-spec bayesian-mc-example-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex/extend-environment
      (support/extend-with :ahof-weighted-estimators
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
