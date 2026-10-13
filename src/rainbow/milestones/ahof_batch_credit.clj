(ns rainbow.milestones.ahof-batch-credit
  "Batch credit of pending AHoF catalog rows whose native axiom-free proofs already
  exist in id-tagged logic modules, via the generic module-credit runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.astar :as m0]
            [rainbow.algorithms.proofs.ahof.baseline-subtraction :as m1]
            [rainbow.algorithms.proofs.ahof.bayesian-optimization :as m2]
            [rainbow.algorithms.proofs.ahof.belief-propagation :as m3]
            [rainbow.algorithms.proofs.ahof.cmaes :as m4]
            [rainbow.algorithms.proofs.ahof.concrete-reachability :as m5]
            [rainbow.algorithms.proofs.ahof.cross-entropy :as m6]
            [rainbow.algorithms.proofs.ahof.direct-sampling :as m7]
            [rainbow.algorithms.proofs.ahof.dual-simplex :as m8]
            [rainbow.algorithms.proofs.ahof.em :as m9]
            [rainbow.algorithms.proofs.ahof.expected-improvement :as m10]
            [rainbow.algorithms.proofs.ahof.falsification :as m11]
            [rainbow.algorithms.proofs.ahof.forward-search :as m12]
            [rainbow.algorithms.proofs.ahof.fuzzing :as m13]
            [rainbow.algorithms.proofs.ahof.gae :as m14]
            [rainbow.algorithms.proofs.ahof.gaussian-inference :as m15]
            [rainbow.algorithms.proofs.ahof.hmc :as m16]
            [rainbow.algorithms.proofs.ahof.k2 :as m17]
            [rainbow.algorithms.proofs.ahof.kernel-smoothing :as m18]
            [rainbow.algorithms.proofs.ahof.kkt :as m19]
            [rainbow.algorithms.proofs.ahof.linear-regression-vf :as m20]
            [rainbow.algorithms.proofs.ahof.mcts :as m21]
            [rainbow.algorithms.proofs.ahof.mesh-adaptive :as m22]
            [rainbow.algorithms.proofs.ahof.natural-gradient :as m23]
            [rainbow.algorithms.proofs.ahof.neural-vf :as m24]
            [rainbow.algorithms.proofs.ahof.pc :as m25]
            [rainbow.algorithms.proofs.ahof.ppo :as m26]
            [rainbow.algorithms.proofs.ahof.rbf-surrogate :as m27]
            [rainbow.algorithms.proofs.ahof.receding-horizon :as m28]
            [rainbow.algorithms.proofs.ahof.rejection-sampling :as m29]
            [rainbow.algorithms.proofs.ahof.rollout :as m30]
            [rainbow.algorithms.proofs.ahof.sac :as m31]
            [rainbow.algorithms.proofs.ahof.sat :as m32]
            [rainbow.algorithms.proofs.ahof.shooting :as m33]
            [rainbow.algorithms.proofs.ahof.simplex :as m34]
            [rainbow.algorithms.proofs.ahof.simplex-interpolation :as m35]
            [rainbow.algorithms.proofs.ahof.trpo :as m36]
            [rainbow.algorithms.proofs.ahof.ucb :as m37]
            [rainbow.algorithms.proofs.ahof.variable-elimination :as m38]))

(def configs
  [
   {:id "D37" :name "A* / Heuristic Search"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D37 A* / heuristic search: the priority by which A* expands nodes is the"
    :kind :ahof-d37-astar
    :dir "artifacts/ahof/d37-astar"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'astar/admissibility-bound
    :spec {:module 'astar :headline 'astar/admissibility-bound}}
   {:id "D48" :name "Baseline Subtraction"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D48 Baseline Subtraction: the variance-reduction wrapper for"
    :kind :ahof-d48-baseline
    :dir "artifacts/ahof/d48-baseline"
    :modules [{:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'baseline/zero-advantage-cancels
    :spec {:module 'baseline :headline 'baseline/zero-advantage-cancels}}
   {:id "O65" :name "Bayesian Optimization Loop"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O65 Bayesian Optimization Loop: iterate (fit surrogate -> maximize"
    :kind :ahof-o65-bayesopt
    :dir "artifacts/ahof/o65-bayesopt"
    :modules [{:extend m2/extend-environment :defs m2/definition-ids :thms m2/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'bayesopt/incumbent-dominates-candidate
    :spec {:module 'bayesopt :headline 'bayesopt/incumbent-dominates-candidate}}
   {:id "D4" :name "Sum-Product (Belief Propagation)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D4 Sum-Product (Belief Propagation): approximate marginal inference by"
    :kind :ahof-d4-belief-propagation
    :dir "artifacts/ahof/d4-belief-propagation"
    :modules [{:extend m3/extend-environment :defs m3/definition-ids :thms m3/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'belief-propagation/zero-message-annihilates
    :spec {:module 'belief-propagation :headline 'belief-propagation/zero-message-annihilates}}
   {:id "O42" :name "CMA-ES"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O42 CMA-ES (Covariance Matrix Adaptation Evolution Strategy) -- the mean"
    :kind :ahof-o42-cmaes
    :dir "artifacts/ahof/o42-cmaes"
    :modules [{:extend m4/extend-environment :defs m4/definition-ids :thms m4/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'cmaes/recombine-example
    :spec {:module 'cmaes :headline 'cmaes/recombine-example}}
   {:id "V44" :name "Concrete Reachability"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V44 Concrete Reachability: the simplest reachability analysis -- push a"
    :kind :ahof-v44-reachability
    :dir "artifacts/ahof/v44-reachability"
    :modules [{:extend m5/extend-environment :defs m5/definition-ids :thms m5/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'reachability/reach-step-empty
    :spec {:module 'reachability :headline 'reachability/reach-step-empty}}
   {:id "O41" :name "Cross-Entropy Method"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O41 Cross-Entropy Method: a model-based stochastic optimizer that, each"
    :kind :ahof-o41-cross-entropy
    :dir "artifacts/ahof/o41-cross-entropy"
    :modules [{:extend m6/extend-environment :defs m6/definition-ids :thms m6/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'cross-entropy/excludes-non-elite
    :spec {:module 'cross-entropy :headline 'cross-entropy/excludes-non-elite}}
   {:id "D5" :name "Direct Sampling"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D5 Direct Sampling: draw a sample from a Bayesian network by ancestral"
    :kind :ahof-d5-direct-sampling
    :dir "artifacts/ahof/d5-direct-sampling"
    :modules [{:extend m7/extend-environment :defs m7/definition-ids :thms m7/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'direct-sampling/skips-below-draw
    :spec {:module 'direct-sampling :headline 'direct-sampling/skips-below-draw}}
   {:id "O55" :name "Dual Simplex"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O55 Dual Simplex Method: solve a linear program by maintaining DUAL"
    :kind :ahof-o55-dual-simplex
    :dir "artifacts/ahof/o55-dual-simplex"
    :modules [{:extend m8/extend-environment :defs m8/definition-ids :thms m8/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'dual-simplex/chosen-ratio-is-minimal
    :spec {:module 'dual-simplex :headline 'dual-simplex/chosen-ratio-is-minimal}}
   {:id "D13" :name "EM Algorithm"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D13 EM Algorithm: fit latent-variable model parameters by alternating an"
    :kind :ahof-d13-em
    :dir "artifacts/ahof/d13-em"
    :modules [{:extend m9/extend-environment :defs m9/definition-ids :thms m9/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'em/converged-at-fixed-point
    :spec {:module 'em :headline 'em/converged-at-fixed-point}}
   {:id "O63" :name "Expected Improvement"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O63 Expected Improvement acquisition (Bayesian optimization). EI balances"
    :kind :ahof-o63-expected-improvement
    :dir "artifacts/ahof/o63-expected-improvement"
    :modules [{:extend m10/extend-environment :defs m10/definition-ids :thms m10/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'expected-improvement/ei-at-least-exploitation
    :spec {:module 'expected-improvement :headline 'expected-improvement/ei-at-least-exploitation}}
   {:id "V9" :name "Direct Sampling Falsification"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V9 Direct Sampling Falsification: the simplest falsification method --"
    :kind :ahof-v9-falsification
    :dir "artifacts/ahof/v9-falsification"
    :modules [{:extend m11/extend-environment :defs m11/definition-ids :thms m11/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'falsification/robust-not-flagged
    :spec {:module 'falsification :headline 'falsification/robust-not-flagged}}
   {:id "D33" :name "Forward Search"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D33 Forward Search: finite-horizon lookahead planning. Building the search"
    :kind :ahof-d33-forward-search
    :dir "artifacts/ahof/d33-forward-search"
    :modules [{:extend m12/extend-environment :defs m12/definition-ids :thms m12/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'forward-search/lookahead-above-b
    :spec {:module 'forward-search :headline 'forward-search/lookahead-above-b}}
   {:id "V11" :name "Fuzzing"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V11 Fuzzing: generate test inputs by repeatedly mutating a seed input and"
    :kind :ahof-v11-fuzzing
    :dir "artifacts/ahof/v11-fuzzing"
    :modules [{:extend m13/extend-environment :defs m13/definition-ids :thms m13/theorem-ids}]
    :baseline-prereqs [{:target/name 'logic/if-data :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'fuzzing/flip-involution-false
    :spec {:module 'fuzzing :headline 'fuzzing/flip-involution-false}}
   {:id "D42" :name "Cross-Entropy for Policies"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D42 Generalized Advantage Estimation: estimate the advantage function as"
    :kind :ahof-d42-gae
    :dir "artifacts/ahof/d42-gae"
    :modules [{:extend m14/extend-environment :defs m14/definition-ids :thms m14/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'gae/collapses-to-td
    :spec {:module 'gae :headline 'gae/collapses-to-td}}
   {:id "D9" :name "Inference in Gaussian Models"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D9 Inference in Gaussian Models: exact closed-form conjugate updates. In"
    :kind :ahof-d9-gaussian
    :dir "artifacts/ahof/d9-gaussian"
    :modules [{:extend m15/extend-environment :defs m15/definition-ids :thms m15/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'gaussian/precision-increases
    :spec {:module 'gaussian :headline 'gaussian/precision-increases}}
   {:id "V24" :name "Hamiltonian Monte Carlo"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V24 Hamiltonian Monte Carlo -- the leapfrog integrator that simulates"
    :kind :ahof-v24-hmc
    :dir "artifacts/ahof/v24-hmc"
    :modules [{:extend m16/extend-environment :defs m16/definition-ids :thms m16/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'hmc/drift-unit-3d-example
    :spec {:module 'hmc :headline 'hmc/drift-unit-3d-example}}
   {:id "D15" :name "K2 Graph Search"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D15 K2 Graph Search: greedy Bayesian-network structure learning. Following"
    :kind :ahof-d15-k2
    :dir "artifacts/ahof/d15-k2"
    :modules [{:extend m17/extend-environment :defs m17/definition-ids :thms m17/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'k2/rejects-non-improvement
    :spec {:module 'k2 :headline 'k2/rejects-non-improvement}}
   {:id "D26" :name "Kernel Smoothing VF"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D26 Kernel Smoothing value-function approximation: approximate the value"
    :kind :ahof-d26-kernel-smoothing
    :dir "artifacts/ahof/d26-kernel-smoothing"
    :modules [{:extend m18/extend-environment :defs m18/definition-ids :thms m18/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'kernel-smoothing/weight-total-example
    :spec {:module 'kernel-smoothing :headline 'kernel-smoothing/weight-total-example}}
   {:id "O53" :name "Lagrange Multipliers (KKT)"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O53 Lagrange Multipliers (KKT): the stationarity condition of the"
    :kind :ahof-o53-kkt
    :dir "artifacts/ahof/o53-kkt"
    :modules [{:extend m19/extend-environment :defs m19/definition-ids :thms m19/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'kkt/stationarity-3d-example
    :spec {:module 'kkt :headline 'kkt/stationarity-3d-example}}
   {:id "D29" :name "Linear Regression VF"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D29 Linear Regression Value Function: approximate the value function as a"
    :kind :ahof-d29-linear-vf
    :dir "artifacts/ahof/d29-linear-vf"
    :modules [{:extend m20/extend-environment :defs m20/definition-ids :thms m20/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'linear-vf/predict-example
    :spec {:module 'linear-vf :headline 'linear-vf/predict-example}}
   {:id "D36" :name "Monte Carlo Tree Search"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D36 Monte Carlo Tree Search: incrementally grow a search tree by"
    :kind :ahof-d36-mcts
    :dir "artifacts/ahof/d36-mcts"
    :modules [{:extend m21/extend-environment :defs m21/definition-ids :thms m21/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'mcts/dominates-third
    :spec {:module 'mcts :headline 'mcts/dominates-third}}
   {:id "O39" :name "Mesh Adaptive Direct Search"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O39 Mesh Adaptive Direct Search (MADS): a derivative-free direct-search"
    :kind :ahof-o39-mads
    :dir "artifacts/ahof/o39-mads"
    :modules [{:extend m22/extend-environment :defs m22/definition-ids :thms m22/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'mads/poll-unit-3d-example
    :spec {:module 'mads :headline 'mads/poll-unit-3d-example}}
   {:id "D50" :name "Natural Gradient"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D50 Natural Gradient: the policy update that ascends along the natural"
    :kind :ahof-d50-natural-gradient
    :dir "artifacts/ahof/d50-natural-gradient"
    :modules [{:extend m23/extend-environment :defs m23/definition-ids :thms m23/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'natural-gradient/update-unit-3d-example
    :spec {:module 'natural-gradient :headline 'natural-gradient/update-unit-3d-example}}
   {:id "D30" :name "Neural Network VF"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D30 Neural Network Value Function: approximate the value function with a"
    :kind :ahof-d30-neural-vf
    :dir "artifacts/ahof/d30-neural-vf"
    :modules [{:extend m24/extend-environment :defs m24/definition-ids :thms m24/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'neural-vf/neuron-above-bias
    :spec {:module 'neural-vf :headline 'neural-vf/neuron-above-bias}}
   {:id "D16" :name "PC Algorithm"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D16 PC Algorithm: constraint-based Bayesian-network structure learning."
    :kind :ahof-d16-pc
    :dir "artifacts/ahof/d16-pc"
    :modules [{:extend m25/extend-environment :defs m25/definition-ids :thms m25/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'pc/keeps-dependent-edge
    :spec {:module 'pc :headline 'pc/keeps-dependent-edge}}
   {:id "D43" :name "Evolution Strategies"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D43 Proximal Policy Optimization: a policy-gradient method that keeps"
    :kind :ahof-d43-ppo
    :dir "artifacts/ahof/d43-ppo"
    :modules [{:extend m26/extend-environment :defs m26/definition-ids :thms m26/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'logic/if-data :statement "shared exact-rational prerequisite is present"}]
    :package 'ppo/passes-in-band
    :spec {:module 'ppo :headline 'ppo/passes-in-band}}
   {:id "O61" :name "RBF Surrogate"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O61 Radial Basis Function surrogate: an interpolating surrogate model that"
    :kind :ahof-o61-rbf
    :dir "artifacts/ahof/o61-rbf"
    :modules [{:extend m27/extend-environment :defs m27/definition-ids :thms m27/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'rbf/predict-single-basis
    :spec {:module 'rbf :headline 'rbf/predict-single-basis}}
   {:id "D31" :name "Receding Horizon"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D31 Receding Horizon Control (model-predictive control): rather than"
    :kind :ahof-d31-mpc
    :dir "artifacts/ahof/d31-mpc"
    :modules [{:extend m28/extend-environment :defs m28/definition-ids :thms m28/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'mpc/first-action-empty
    :spec {:module 'mpc :headline 'mpc/first-action-empty}}
   {:id "V21" :name "Rejection Sampling (Failures)"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V21 Rejection Sampling (for failure events): draw samples and keep only"
    :kind :ahof-v21-rejection
    :dir "artifacts/ahof/v21-rejection"
    :modules [{:extend m29/extend-environment :defs m29/definition-ids :thms m29/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'rejection/rejects-inconsistent
    :spec {:module 'rejection :headline 'rejection/rejects-inconsistent}}
   {:id "D32" :name "Rollout with Heuristic"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D32 Rollout with Heuristic: estimate a state's value by simulating the"
    :kind :ahof-d32-rollout
    :dir "artifacts/ahof/d32-rollout"
    :modules [{:extend m30/extend-environment :defs m30/definition-ids :thms m30/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'rollout/return-dominates-step
    :spec {:module 'rollout :headline 'rollout/return-dominates-step}}
   {:id "D45" :name "Finite Difference Gradient"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D45 Soft Actor-Critic: an off-policy actor-critic that optimizes a"
    :kind :ahof-d45-sac
    :dir "artifacts/ahof/d45-sac"
    :modules [{:extend m31/extend-environment :defs m31/definition-ids :thms m31/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'sac/collapses-to-reward
    :spec {:module 'sac :headline 'sac/collapses-to-reward}}
   {:id "V50" :name "SAT-Based Bounded Model Check"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V50 SAT-based Bounded Model Checking: the system is unrolled k steps and"
    :kind :ahof-v50-sat
    :dir "artifacts/ahof/v50-sat"
    :modules [{:extend m32/extend-environment :defs m32/definition-ids :thms m32/theorem-ids}]
    :baseline-prereqs [{:target/name 'logic/if-data :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'sat/clause-empty
    :spec {:module 'sat :headline 'sat/clause-empty}}
   {:id "V16" :name "Shooting Methods"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V16 Shooting Methods: trajectory-based trajectory optimization / open-loop"
    :kind :ahof-v16-shooting
    :dir "artifacts/ahof/v16-shooting"
    :modules [{:extend m33/extend-environment :defs m33/definition-ids :thms m33/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'shooting/simulate-example
    :spec {:module 'shooting :headline 'shooting/simulate-example}}
   {:id "O54" :name "Simplex Algorithm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O54 Simplex Algorithm -- the minimum-ratio test that chooses the leaving"
    :kind :ahof-o54-simplex
    :dir "artifacts/ahof/o54-simplex"
    :modules [{:extend m34/extend-environment :defs m34/definition-ids :thms m34/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'simplex/pivot-below-r2
    :spec {:module 'simplex :headline 'simplex/pivot-below-r2}}
   {:id "D28" :name "Simplex Interpolation"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D28 Simplex Interpolation: interpolate a value function over a simplicial"
    :kind :ahof-d28-simplex-interpolation
    :dir "artifacts/ahof/d28-simplex-interpolation"
    :modules [{:extend m35/extend-environment :defs m35/definition-ids :thms m35/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'simplex-interpolation/interpolate-at-vertex
    :spec {:module 'simplex-interpolation :headline 'simplex-interpolation/interpolate-at-vertex}}
   {:id "D51" :name "Trust Region Policy Opt"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D51 Trust-Region Policy Optimization: improve a policy by maximizing a"
    :kind :ahof-d51-trpo
    :dir "artifacts/ahof/d51-trpo"
    :modules [{:extend m36/extend-environment :defs m36/definition-ids :thms m36/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'trpo/oversized-update-rejected
    :spec {:module 'trpo :headline 'trpo/oversized-update-rejected}}
   {:id "O64" :name "Upper Confidence Bound"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O64 Upper Confidence Bound acquisition (Bayesian optimization / bandits):"
    :kind :ahof-o64-ucb
    :dir "artifacts/ahof/o64-ucb"
    :modules [{:extend m37/extend-environment :defs m37/definition-ids :thms m37/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'ucb/at-least-mean
    :spec {:module 'ucb :headline 'ucb/at-least-mean}}
   {:id "D3" :name "Variable Elimination"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D3 Variable Elimination: exact inference by successively eliminating"
    :kind :ahof-d3-variable-elimination
    :dir "artifacts/ahof/d3-variable-elimination"
    :modules [{:extend m38/extend-environment :defs m38/definition-ids :thms m38/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'variable-elimination/marginal-dominates-slice
    :spec {:module 'variable-elimination :headline 'variable-elimination/marginal-dominates-slice}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs
                          (Integer/parseInt (first args))
                          (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
