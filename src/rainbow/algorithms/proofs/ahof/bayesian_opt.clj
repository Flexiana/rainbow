(ns rainbow.algorithms.proofs.ahof.bayesian-opt
  "Kochenderfer surrogate-optimization / model-validation cores as higher-order-function
  compositions, proved axiom-free, extending the 222 AHoF catalog:

    O19.1 probability of improvement : acquisition prefers candidates beating the best
    O19.3 SafeOpt                    : query only within the high-confidence safe set
    O17.14 0.632 bootstrap           : convex combo 0.368*train + 0.632*test error
    O17.12 bootstrap generalization  : mean holdout error over resamples

  Improvement / safety are decidable-order tests with soundness (decide-at-most-true-
  sound); the bootstrap estimators reuse nnrat/wsum2 (bounded by the convex bound).
  Native and axiom-free; chains nnrat-convex (-> wsum2, minmax) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))

(defn- wsum2 [w0 w1 v0 v1] (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- decide-at-most [a b] (function/app (function/const* 'audit/decide-nnrat-at-most []) a b))
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

;; ---- O19.1 probability of improvement ---------------------------------------
(def is-improvement-spec
  {:name 'bo/is-improvement :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['candidate nnrat] ['best nnrat]] (decide-at-most 'best 'candidate))})

(def improvement-sound-spec
  {:name 'bo/improvement-sound :universes []
   :type (function/forall [['candidate nnrat] ['best nnrat]
                           ['ok (eq-bool (function/app (function/const* 'bo/is-improvement []) 'candidate 'best)
                                         true-value)]]
                          (at-most 'best 'candidate))
   :value (function/lam [['candidate nnrat] ['best nnrat]
                         ['ok (eq-bool (function/app (function/const* 'bo/is-improvement []) 'candidate 'best)
                                       true-value)]]
                        (function/app (function/const* 'nnrat/decide-at-most-true-sound []) 'best 'candidate 'ok))})

;; ---- O19.3 SafeOpt safe-set membership --------------------------------------
(def is-safe-spec
  {:name 'bo/is-safe :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['lcb nnrat] ['threshold nnrat]] (decide-at-most 'threshold 'lcb))})

(def safe-sound-spec
  {:name 'bo/safe-sound :universes []
   :type (function/forall [['lcb nnrat] ['threshold nnrat]
                           ['ok (eq-bool (function/app (function/const* 'bo/is-safe []) 'lcb 'threshold)
                                         true-value)]]
                          (at-most 'threshold 'lcb))
   :value (function/lam [['lcb nnrat] ['threshold nnrat]
                         ['ok (eq-bool (function/app (function/const* 'bo/is-safe []) 'lcb 'threshold)
                                       true-value)]]
                        (function/app (function/const* 'nnrat/decide-at-most-true-sound []) 'threshold 'lcb 'ok))})

;; ---- O17.14 0.632 bootstrap (convex combo of train and test error) ----------
(def bootstrap-632-spec
  {:name 'bo/bootstrap-632 :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w-train nnrat] ['w-test nnrat] ['train nnrat] ['test nnrat]]
                        (wsum2 'w-train 'w-test 'train 'test))})

;; with weights summing to one (0.368, 0.632) the estimate is bounded by the larger error
(def bootstrap-632-within-max-spec
  {:name 'bo/bootstrap-632-within-max :universes []
   :type (function/forall [['w-train nnrat] ['w-test nnrat] ['train nnrat] ['test nnrat]
                           ['hw (equiv (radd 'w-train 'w-test) rone)]]
                          (at-most (function/app (function/const* 'bo/bootstrap-632 [])
                                                 'w-train 'w-test 'train 'test)
                                   (rmax 'train 'test)))
   :value (function/lam [['w-train nnrat] ['w-test nnrat] ['train nnrat] ['test nnrat]
                         ['hw (equiv (radd 'w-train 'w-test) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w-train 'w-test 'train 'test 'hw))})

;; ---- O17.12 bootstrap generalization error (mean over resamples) ------------
(def bootstrap-mean-spec
  {:name 'bo/bootstrap-mean :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['e0 nnrat] ['e1 nnrat]]
                        (wsum2 'w0 'w1 'e0 'e1))})

;; worked: equal weights over resample errors (1,0) -> mean 1/2
(def bootstrap-mean-example-spec
  {:name 'bo/bootstrap-mean-example :universes []
   :type (equiv (function/app (function/const* 'bo/bootstrap-mean []) half half rone (rational 0 0))
                (rational 1 1))
   :value (equiv-cross (function/app (function/const* 'bo/bootstrap-mean []) half half rone (rational 0 0))
                       (rational 1 1))})

(def definition-specs
  [is-improvement-spec is-safe-spec bootstrap-632-spec bootstrap-mean-spec])
(def theorem-specs
  [improvement-sound-spec safe-sound-spec bootstrap-632-within-max-spec bootstrap-mean-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-bayesian-opt (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.bayesian-opt))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
