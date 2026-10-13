(ns rainbow.algorithms.proofs.ahof.sequential-decision
  "Kochenderfer 'Algorithms for Decision Making' game-theory + model-based-RL cores as
  higher-order-function compositions, proved axiom-free, extending the 222 AHoF catalog:

    D24.8 iterated best response : best-response value = max over own actions (dominates)
    D16.7 R-MAX                  : optimistic value = max(realistic, Vmax); optimism bound
    D16.5 prioritized sweeping   : sweep the state of maximum Bellman-residual priority
    D16.4 model-based RL (Dyna)  : certainty-equivalence value = expectation over model
    D17.6 Q-learning w/ replay   : replay target = reward + discount * max_a Q(s',a)

  Selection/optimism/priority reuse nnrat-minmax; the certainty-equivalence value and
  the replay Bellman target reuse nnrat/wsum2 and nnrat add/multiply.
  Native and axiom-free; chains nnrat-convex (-> wsum2, minmax) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

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

;; ---- D24.8 iterated best response --------------------------------------------
(def best-response-spec
  {:name 'game/best-response-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p0 nnrat] ['p1 nnrat]] (rmax 'p0 'p1))})

(def best-response-dominates-spec
  {:name 'game/best-response-dominates :universes []
   :type (function/forall [['p0 nnrat] ['p1 nnrat]]
                          (at-most 'p0 (function/app (function/const* 'game/best-response-value []) 'p0 'p1)))
   :value (function/lam [['p0 nnrat] ['p1 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'p0 'p1))})

;; ---- D16.7 R-MAX: optimism under uncertainty ---------------------------------
(def rmax-value-spec
  {:name 'rl/rmax-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['realistic nnrat] ['vmax nnrat]] (rmax 'realistic 'vmax))})

;; the optimistic value never underestimates the realistic value (drives exploration)
(def rmax-optimistic-spec
  {:name 'rl/rmax-optimistic :universes []
   :type (function/forall [['realistic nnrat] ['vmax nnrat]]
                          (at-most 'realistic (function/app (function/const* 'rl/rmax-value []) 'realistic 'vmax)))
   :value (function/lam [['realistic nnrat] ['vmax nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'realistic 'vmax))})

;; ---- D16.5 prioritized sweeping: sweep the max-residual state -----------------
(def sweep-priority-spec
  {:name 'rl/sweep-priority :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['r0 nnrat] ['r1 nnrat]] (rmax 'r0 'r1))})

(def sweep-picks-max-priority-spec
  {:name 'rl/sweep-picks-max-priority :universes []
   :type (function/forall [['r0 nnrat] ['r1 nnrat]]
                          (at-most 'r1 (function/app (function/const* 'rl/sweep-priority []) 'r0 'r1)))
   :value (function/lam [['r0 nnrat] ['r1 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-right []) 'r0 'r1))})

;; ---- D16.4 model-based RL (certainty equivalence): expectation over model -----
(def model-based-value-spec
  {:name 'rl/model-based-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['p0 nnrat] ['p1 nnrat] ['v0 nnrat] ['v1 nnrat]]
                        (wsum2 'p0 'p1 'v0 'v1))})

;; worked: learned transition p=(1/2,1/2) over next values (1,0) -> value 1/2
(def model-based-example-spec
  {:name 'rl/model-based-example :universes []
   :type (equiv (function/app (function/const* 'rl/model-based-value [])
                              (rational 1 1) (rational 1 1) (rational 1 0) (rational 0 0))
                (rational 1 1))
   :value (equiv-cross (function/app (function/const* 'rl/model-based-value [])
                                     (rational 1 1) (rational 1 1) (rational 1 0) (rational 0 0))
                       (rational 1 1))})

;; ---- D17.6 Q-learning with experience replay: Bellman target -----------------
(def replay-target-spec
  {:name 'rl/replay-target :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['reward nnrat] ['discount nnrat] ['q0 nnrat] ['q1 nnrat]]
                        (radd 'reward (rmul 'discount (rmax 'q0 'q1))))})

;; worked: reward 1, discount 1/2, next Q = (1,0) -> target 1 + 1/2*1 = 3/2
(def replay-target-example-spec
  {:name 'rl/replay-target-example :universes []
   :type (equiv (function/app (function/const* 'rl/replay-target [])
                              (rational 1 0) (rational 1 1) (rational 1 0) (rational 0 0))
                (rational 3 1))
   :value (equiv-cross (function/app (function/const* 'rl/replay-target [])
                                     (rational 1 0) (rational 1 1) (rational 1 0) (rational 0 0))
                       (rational 3 1))})

(def definition-specs
  [best-response-spec rmax-value-spec sweep-priority-spec
   model-based-value-spec replay-target-spec])
(def theorem-specs
  [best-response-dominates-spec rmax-optimistic-spec sweep-picks-max-priority-spec
   model-based-example-spec replay-target-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-sequential-decision (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.sequential-decision))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
