(ns rainbow.algorithms.proofs.ahof.imitation-irl
  "Kochenderfer imitation-learning / inverse-RL / structure-learning cores as
  higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog:

    D18.3 SMILe            : stochastic mixture of expert-imitating policies (convex blend)
    D18.5 max-margin IRL   : reward makes the expert beat alternatives by a margin (sound)
    D18.6 max-entropy IRL  : trajectory probability = exp-weight / partition (normalized)
    D5.3  structure learning: hill-climb the DAG by score (accepted neighbor >= current)

  The SMILe blend reuses nnrat/wsum2 (bounded by convex-at-most-max); the margin test is
  a decidable order on expert-vs-(alternative+margin) with soundness; max-entropy is a
  normalized weight (divide); structure search reuses nnrat-minmax max.
  Native and axiom-free; chains nnrat-convex on d63."
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
(defn- rdiv [a b] (function/app (function/const* 'nnrat/divide []) a b))
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

;; ---- D18.3 SMILe: convex mixture of policies --------------------------------
(def smile-mixture-spec
  {:name 'irl/smile-mixture :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['p0 nnrat] ['p1 nnrat]]
                        (wsum2 'w0 'w1 'p0 'p1))})

(def smile-within-max-spec
  {:name 'irl/smile-within-max :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['p0 nnrat] ['p1 nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'irl/smile-mixture []) 'w0 'w1 'p0 'p1)
                                   (rmax 'p0 'p1)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['p0 nnrat] ['p1 nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'p0 'p1 'hw))})

;; ---- D18.5 max-margin IRL: expert beats alternative by a margin --------------
(def margin-satisfied-spec
  {:name 'irl/margin-satisfied :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam [['expert nnrat] ['alt nnrat] ['margin nnrat]]
                        (decide-at-most (radd 'alt 'margin) 'expert))})

(def margin-sound-spec
  {:name 'irl/margin-sound :universes []
   :type (function/forall [['expert nnrat] ['alt nnrat] ['margin nnrat]
                           ['ok (eq-bool (function/app (function/const* 'irl/margin-satisfied [])
                                                       'expert 'alt 'margin) true-value)]]
                          (at-most (radd 'alt 'margin) 'expert))
   :value (function/lam [['expert nnrat] ['alt nnrat] ['margin nnrat]
                         ['ok (eq-bool (function/app (function/const* 'irl/margin-satisfied [])
                                                     'expert 'alt 'margin) true-value)]]
                        (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                                      (radd 'alt 'margin) 'expert 'ok))})

;; ---- D18.6 max-entropy IRL: normalized exp-weight probability ----------------
(def maxent-probability-spec
  {:name 'irl/maxent-probability :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['weight nnrat] ['partition nnrat]] (rdiv 'weight 'partition))})

;; worked: exp-weight 3, partition 4 -> trajectory probability 3/4
(def maxent-probability-example-spec
  {:name 'irl/maxent-probability-example :universes []
   :type (equiv (function/app (function/const* 'irl/maxent-probability []) (rational 3 0) (rational 4 0))
                (rational 3 3))
   :value (equiv-cross (function/app (function/const* 'irl/maxent-probability []) (rational 3 0) (rational 4 0))
                       (rational 3 3))})

;; ---- D5.3 structure learning: hill-climb the DAG by score -------------------
(def structure-accept-spec
  {:name 'learn/structure-accept :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current nnrat] ['neighbor nnrat]] (rmax 'current 'neighbor))})

(def structure-improves-spec
  {:name 'learn/structure-improves :universes []
   :type (function/forall [['current nnrat] ['neighbor nnrat]]
                          (at-most 'current (function/app (function/const* 'learn/structure-accept [])
                                                          'current 'neighbor)))
   :value (function/lam [['current nnrat] ['neighbor nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'current 'neighbor))})

(def definition-specs
  [smile-mixture-spec margin-satisfied-spec maxent-probability-spec structure-accept-spec])
(def theorem-specs
  [smile-within-max-spec margin-sound-spec maxent-probability-example-spec structure-improves-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-imitation-irl (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.imitation-irl))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
