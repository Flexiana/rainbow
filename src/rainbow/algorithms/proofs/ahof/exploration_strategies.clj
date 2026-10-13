(ns rainbow.algorithms.proofs.ahof.exploration-strategies
  "Kochenderfer 'Algorithms for Decision Making' Ch.15 bandit exploration strategies,
  expressed as higher-order-function compositions and proved axiom-free (core structural
  property per algorithm), extending the 222 AHoF catalog:

    D15.3 epsilon-greedy        : explore/exploit branch (Bool) over a random bit
    D15.4 explore-then-commit   : two-phase branch on a round>=k threshold (decide-at-most)
    D15.5 softmax exploration   : stochastic policy, probability = weight / total (divide)
    D15.6 quantile exploration  : optimistic additive bonus (mean + bonus), pick the max

  Greedy exploitation reuses rainbow.math.rational.nnrat.minmax (max dominates both arms).
  Native and axiom-free; chains nnrat-minmax on the d63 base."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rdiv [a b] (function/app (function/const* 'nnrat/divide []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- eq-nnrat [l r] (function/equality type-level nnrat l r))
(defn- if-data [cond decision then else]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat cond decision then else))
(defn- reflexive-nnrat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nnrat v))
;; cross-product equivalence certificate: equivalent x lit  <=  reflexive on num(x)*den(lit)
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(def ^:private nat (function/const* 'data/Nat []))
(defn- equiv-cross [x lit]
  (function/app (function/const* 'equality/reflexive [type-level]) nat
                (nmul (num x) (den lit))))

(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- numeral [n] (nth (iterate succ zero-nat) n))
(defn- rational [n d-pred]
  (function/app (function/const* 'nnrat/make []) (numeral n) (numeral d-pred)))

;; ---------------------------------------------------------------------------
;; D15.3 epsilon-greedy: with the explore bit, act randomly; else exploit greedy.
;;   epsilon-greedy cond bit exploit random = if bit then random else exploit
(def epsilon-greedy-spec
  {:name 'explore/epsilon-greedy :kind :definition :universes []
   :type (function/arrow 'Prop bool nnrat nnrat nnrat)
   :value (function/lam [['cond 'Prop] ['bit bool] ['exploit nnrat] ['random nnrat]]
                        (if-data 'cond 'bit 'random 'exploit))})

;; exploit branch (bit=false) returns the greedy/exploit value
(def epsilon-greedy-exploits-spec
  {:name 'explore/epsilon-greedy-exploits :universes []
   :type (function/forall [['cond 'Prop] ['exploit nnrat] ['random nnrat]]
                          (eq-nnrat (function/app (function/const* 'explore/epsilon-greedy [])
                                                  'cond false-value 'exploit 'random)
                                    'exploit))
   :value (function/lam [['cond 'Prop] ['exploit nnrat] ['random nnrat]]
                        (reflexive-nnrat 'exploit))})

;; explore branch (bit=true) returns the random value
(def epsilon-greedy-explores-spec
  {:name 'explore/epsilon-greedy-explores :universes []
   :type (function/forall [['cond 'Prop] ['exploit nnrat] ['random nnrat]]
                          (eq-nnrat (function/app (function/const* 'explore/epsilon-greedy [])
                                                  'cond true-value 'exploit 'random)
                                    'random))
   :value (function/lam [['cond 'Prop] ['exploit nnrat] ['random nnrat]]
                        (reflexive-nnrat 'random))})

;; the greedy/exploit value is the max of the arm estimates and dominates each arm
(def greedy-value-spec
  {:name 'explore/greedy-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['v0 nnrat] ['v1 nnrat]] (rmax 'v0 'v1))})

(def greedy-dominates-left-spec
  {:name 'explore/greedy-dominates-left :universes []
   :type (function/forall [['v0 nnrat] ['v1 nnrat]]
                          (at-most 'v0 (function/app (function/const* 'explore/greedy-value []) 'v0 'v1)))
   :value (function/lam [['v0 nnrat] ['v1 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'v0 'v1))})

(def greedy-dominates-right-spec
  {:name 'explore/greedy-dominates-right :universes []
   :type (function/forall [['v0 nnrat] ['v1 nnrat]]
                          (at-most 'v1 (function/app (function/const* 'explore/greedy-value []) 'v0 'v1)))
   :value (function/lam [['v0 nnrat] ['v1 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-right []) 'v0 'v1))})

;; ---------------------------------------------------------------------------
;; D15.4 explore-then-commit: two phases; committed?=decide(k<=round) selects greedy, else uniform.
(def explore-then-commit-spec
  {:name 'explore/explore-then-commit :kind :definition :universes []
   :type (function/arrow 'Prop bool nnrat nnrat nnrat)
   :value (function/lam [['cond 'Prop] ['committed bool] ['greedy nnrat] ['uniform nnrat]]
                        (if-data 'cond 'committed 'greedy 'uniform))})

(def etc-commits-spec
  {:name 'explore/explore-then-commit-commits :universes []
   :type (function/forall [['cond 'Prop] ['greedy nnrat] ['uniform nnrat]]
                          (eq-nnrat (function/app (function/const* 'explore/explore-then-commit [])
                                                  'cond true-value 'greedy 'uniform)
                                    'greedy))
   :value (function/lam [['cond 'Prop] ['greedy nnrat] ['uniform nnrat]]
                        (reflexive-nnrat 'greedy))})

(def etc-explores-spec
  {:name 'explore/explore-then-commit-explores :universes []
   :type (function/forall [['cond 'Prop] ['greedy nnrat] ['uniform nnrat]]
                          (eq-nnrat (function/app (function/const* 'explore/explore-then-commit [])
                                                  'cond false-value 'greedy 'uniform)
                                    'uniform))
   :value (function/lam [['cond 'Prop] ['greedy nnrat] ['uniform nnrat]]
                        (reflexive-nnrat 'uniform))})

;; ---------------------------------------------------------------------------
;; D15.6 quantile exploration: optimistic upper-quantile score = mean + exploration bonus;
;; pick the arm with the larger score (the bonus dominates a zero-bonus arm at equal mean).
(def quantile-score-spec
  {:name 'explore/quantile-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['mean nnrat] ['bonus nnrat]] (radd 'mean 'bonus))})

(def quantile-select-spec
  {:name 'explore/quantile-select :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['q0 nnrat] ['q1 nnrat]] (rmax 'q0 'q1))})

;; worked: means 1/2 and 1/2, bonuses 0 and 1/2 -> scores 1/2 and 1, select 1 (optimism picks arm 1)
(def quantile-optimism-example-spec
  {:name 'explore/quantile-optimism-example :universes []
   :type (equiv (function/app (function/const* 'explore/quantile-select [])
                              (function/app (function/const* 'explore/quantile-score [])
                                            (rational 1 1) (rational 0 0))
                              (function/app (function/const* 'explore/quantile-score [])
                                            (rational 1 1) (rational 1 1)))
                (rational 1 0))
   :value (equiv-cross (function/app (function/const* 'explore/quantile-select [])
                                     (function/app (function/const* 'explore/quantile-score [])
                                                   (rational 1 1) (rational 0 0))
                                     (function/app (function/const* 'explore/quantile-score [])
                                                   (rational 1 1) (rational 1 1)))
                       (rational 1 0))})

;; ---------------------------------------------------------------------------
;; D15.5 softmax (Boltzmann) exploration: stochastic policy, probability = weight / total.
(def softmax-probability-spec
  {:name 'explore/softmax-probability :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['weight nnrat] ['total nnrat]] (rdiv 'weight 'total))})

;; worked: weight 3, total 4 -> probability 3/4
(def softmax-probability-example-spec
  {:name 'explore/softmax-probability-example :universes []
   :type (equiv (function/app (function/const* 'explore/softmax-probability [])
                              (rational 3 0) (rational 4 0))
                (rational 3 3))
   :value (equiv-cross (function/app (function/const* 'explore/softmax-probability [])
                                     (rational 3 0) (rational 4 0))
                       (rational 3 3))})

(def definition-specs
  [epsilon-greedy-spec greedy-value-spec explore-then-commit-spec
   quantile-score-spec quantile-select-spec softmax-probability-spec])

(def theorem-specs
  [epsilon-greedy-exploits-spec epsilon-greedy-explores-spec
   greedy-dominates-left-spec greedy-dominates-right-spec
   etc-commits-spec etc-explores-spec
   quantile-optimism-example-spec softmax-probability-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-exploration-strategies (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.exploration-strategies))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
