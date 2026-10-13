(ns rainbow.algorithms.proofs.sparse-sampling
  "AHoF D35 Sparse Sampling: the sample-complexity count of the sparse-sampling
  MDP planner (Kearns-Mansour-Ng). To estimate the value at a state to horizon H,
  the planner recurses, drawing C sampled next-states for each of the |A| actions
  at every node, so the sampled look-ahead tree has

      node-count |A| C H = (|A| * C) ^ H

  leaves -- exponential in the horizon but INDEPENDENT of the (possibly infinite)
  state-space size, which is the defining property that makes sparse sampling a
  tractable planner for large MDPs. Proved native and axiom-free using exact
  natural exponentiation (nat/power): the count is the branching factor |A|*C
  raised to the horizon. The value backup and the sampling itself are executable
  concerns; what is proved here is the sample-complexity count and worked
  instances.

  Requires nat, nat/multiply, and nat/power (nat/power added alongside).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.sparse-sampling`
  prints this classification."
  (:require [rainbow.math.nat.power :as dep-nat-power]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))

(defn- multiply [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- power [base exp] (function/app (function/const* 'nat/power []) base exp))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- node-count [actions samples horizon]
  (function/app (function/const* 'sparse-sampling/node-count [])
                actions samples horizon))

;; Definitions --------------------------------------------------------------

;; node-count |A| C H = (|A| * C) ^ H
(def node-count-spec
  {:name 'sparse-sampling/node-count :kind :definition :universes []
   :type (function/arrow nat nat nat nat)
   :value (function/lam [['actions nat] ['samples nat] ['horizon nat]]
                        (power (multiply 'actions 'samples) 'horizon))})

(def definition-specs [node-count-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))

;; node-count unfolds to the branching factor raised to the horizon.
(def node-count-is-power-spec
  {:name 'sparse-sampling/node-count-is-power :universes []
   :type (function/forall
          [['actions nat] ['samples nat] ['horizon nat]]
          (equality nat
                    (node-count 'actions 'samples 'horizon)
                    (power (multiply 'actions 'samples) 'horizon)))
   :value (function/lam
           [['actions nat] ['samples nat] ['horizon nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (node-count 'actions 'samples 'horizon)))})

;; A horizon-0 lookahead is a single node (the root), for any |A| and C.
(def horizon-zero-single-node-spec
  {:name 'sparse-sampling/horizon-zero-single-node :universes []
   :type (function/forall
          [['actions nat] ['samples nat]]
          (equality nat
                    (node-count 'actions 'samples (data-nat 0))
                    (data-nat 1)))
   :value (function/lam
           [['actions nat] ['samples nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nat (node-count 'actions 'samples (data-nat 0))))})

;; Worked: 2 actions, 3 samples, horizon 2 -> (2*3)^2 = 36 nodes.
(def node-count-example-spec
  {:name 'sparse-sampling/node-count-example :universes []
   :type (equality nat
                   (node-count (data-nat 2) (data-nat 3) (data-nat 2))
                   (data-nat 36))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (node-count (data-nat 2) (data-nat 3) (data-nat 2)))})

;; Worked: 2 actions, 2 samples, horizon 3 -> (2*2)^3 = 64 nodes.
(def node-count-deep-example-spec
  {:name 'sparse-sampling/node-count-deep-example :universes []
   :type (equality nat
                   (node-count (data-nat 2) (data-nat 2) (data-nat 3))
                   (data-nat 64))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat
                        (node-count (data-nat 2) (data-nat 2) (data-nat 3)))})

(def theorem-specs
  [node-count-is-power-spec horizon-zero-single-node-spec
   node-count-example-spec node-count-deep-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with (dep-nat-power/extend-environment checked-environment) :sparse-sampling
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
