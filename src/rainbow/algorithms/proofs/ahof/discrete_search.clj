(ns rainbow.algorithms.proofs.ahof.discrete-search
  "Kochenderfer discrete-search / sampling / metaheuristic cores as higher-order-function
  compositions, proved axiom-free, extending the 222 AHoF catalog:

    O22.7  0-1 knapsack DP        : cell = max(exclude value, include value)
    V5.4   RRT nearest-node       : steer toward the nearest existing node (min distance)
    V5.8   star discrepancy bound : worst-case box discrepancy = max over sub-boxes
    O22.10 ant colony optimization: pheromone update = evaporation*old + deposit

  DP/coverage reuse nnrat-minmax max (cell/upper-bound dominates each option); the RRT
  nearest reuses min (dominated by both candidates); the pheromone dynamics is an
  add/multiply composition with a worked instance.
  Native and axiom-free; chains nnrat-minmax on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
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

;; ---- O22.7 0-1 knapsack DP recurrence ---------------------------------------
(def knapsack-cell-spec
  {:name 'dp/knapsack-cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['exclude nnrat] ['include nnrat]] (rmax 'exclude 'include))})

(def knapsack-at-least-exclude-spec
  {:name 'dp/knapsack-at-least-exclude :universes []
   :type (function/forall [['exclude nnrat] ['include nnrat]]
                          (at-most 'exclude (function/app (function/const* 'dp/knapsack-cell []) 'exclude 'include)))
   :value (function/lam [['exclude nnrat] ['include nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'exclude 'include))})

(def knapsack-at-least-include-spec
  {:name 'dp/knapsack-at-least-include :universes []
   :type (function/forall [['exclude nnrat] ['include nnrat]]
                          (at-most 'include (function/app (function/const* 'dp/knapsack-cell []) 'exclude 'include)))
   :value (function/lam [['exclude nnrat] ['include nnrat]]
                        (function/app (function/const* 'minmax/max-upper-right []) 'exclude 'include))})

;; ---- V5.4 RRT nearest-node steering -----------------------------------------
(def rrt-nearest-spec
  {:name 'plan/rrt-nearest :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['d0 nnrat] ['d1 nnrat]] (rmin 'd0 'd1))})

(def rrt-nearest-below-left-spec
  {:name 'plan/rrt-nearest-below-left :universes []
   :type (function/forall [['d0 nnrat] ['d1 nnrat]]
                          (at-most (function/app (function/const* 'plan/rrt-nearest []) 'd0 'd1) 'd0))
   :value (function/lam [['d0 nnrat] ['d1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-left []) 'd0 'd1))})

(def rrt-nearest-below-right-spec
  {:name 'plan/rrt-nearest-below-right :universes []
   :type (function/forall [['d0 nnrat] ['d1 nnrat]]
                          (at-most (function/app (function/const* 'plan/rrt-nearest []) 'd0 'd1) 'd1))
   :value (function/lam [['d0 nnrat] ['d1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-right []) 'd0 'd1))})

;; ---- V5.8 star discrepancy upper bound --------------------------------------
(def star-discrepancy-spec
  {:name 'sample/star-discrepancy-upper :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['b1 nnrat]] (rmax 'b0 'b1))})

(def star-discrepancy-bounds-box0-spec
  {:name 'sample/star-discrepancy-bounds-box0 :universes []
   :type (function/forall [['b0 nnrat] ['b1 nnrat]]
                          (at-most 'b0 (function/app (function/const* 'sample/star-discrepancy-upper []) 'b0 'b1)))
   :value (function/lam [['b0 nnrat] ['b1 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'b0 'b1))})

;; ---- O22.10 ant colony: pheromone update (evaporation + deposit) --------------
(def aco-pheromone-update-spec
  {:name 'aco/pheromone-update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['retain nnrat] ['old nnrat] ['deposit nnrat]]
                        (radd (rmul 'retain 'old) 'deposit))})

;; worked: retain 1/2, old 1, deposit 1/2 -> updated pheromone 1
(def aco-pheromone-example-spec
  {:name 'aco/pheromone-update-example :universes []
   :type (equiv (function/app (function/const* 'aco/pheromone-update [])
                              (rational 1 1) (rational 1 0) (rational 1 1)) (rational 1 0))
   :value (equiv-cross (function/app (function/const* 'aco/pheromone-update [])
                                     (rational 1 1) (rational 1 0) (rational 1 1)) (rational 1 0))})

(def definition-specs
  [knapsack-cell-spec rrt-nearest-spec star-discrepancy-spec aco-pheromone-update-spec])
(def theorem-specs
  [knapsack-at-least-exclude-spec knapsack-at-least-include-spec
   rrt-nearest-below-left-spec rrt-nearest-below-right-spec
   star-discrepancy-bounds-box0-spec aco-pheromone-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-discrete-search (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.discrete-search))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
