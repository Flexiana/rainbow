(ns rainbow.milestones.ahof-batch4-credit
  "Fourth batch: pending rows needing specific prerequisite-module chains
  (vector ops, inner product, signed multiply, nat power) before the target."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.math.finite.vector :as m0]
            [rainbow.math.linear.vector.equivalence :as m1]
            [rainbow.algorithms.proofs.nelder-mead :as m2]
            [rainbow.algorithms.proofs.ahof.mesh-adaptive :as m3]
            [rainbow.algorithms.proofs.ahof.cmaes :as m4]
            [rainbow.algorithms.proofs.ahof.kkt :as m5]
            [rainbow.algorithms.proofs.ahof.hmc :as m6]
            [rainbow.math.nat.power :as m7]
            [rainbow.algorithms.proofs.sparse-sampling :as m8]
            [rainbow.algorithms.proofs.inner-product :as m9]
            [rainbow.math.rational.signed.multiply :as m10]
            [rainbow.algorithms.proofs.hypergradient :as m11]
            [rainbow.algorithms.proofs.counterfactual :as m12]))

(def configs
  [
   {:id "O36" :name "Nelder-Mead Simplex"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O36 Nelder-Mead Simplex: the reflection move, the workhorse simplex"
    :kind :ahof-o36-nelder
    :dir "artifacts/ahof/o36-nelder"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m2/extend-environment :defs m2/definition-ids :thms m2/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'nelder/reflect-example
    :spec {:module 'nelder :headline 'nelder/reflect-example}}
   {:id "O39" :name "Mesh Adaptive Direct Search"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O39 Mesh Adaptive Direct Search (MADS): a derivative-free direct-search"
    :kind :ahof-o39-mads
    :dir "artifacts/ahof/o39-mads"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m3/extend-environment :defs m3/definition-ids :thms m3/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'mads/poll-unit-3d-example
    :spec {:module 'mads :headline 'mads/poll-unit-3d-example}}
   {:id "O42" :name "CMA-ES"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O42 CMA-ES (Covariance Matrix Adaptation Evolution Strategy) -- the mean"
    :kind :ahof-o42-cmaes
    :dir "artifacts/ahof/o42-cmaes"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m4/extend-environment :defs m4/definition-ids :thms m4/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'cmaes/recombine-example
    :spec {:module 'cmaes :headline 'cmaes/recombine-example}}
   {:id "O53" :name "Lagrange Multipliers (KKT)"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O53 Lagrange Multipliers (KKT): the stationarity condition of the"
    :kind :ahof-o53-kkt
    :dir "artifacts/ahof/o53-kkt"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m5/extend-environment :defs m5/definition-ids :thms m5/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'kkt/stationarity-3d-example
    :spec {:module 'kkt :headline 'kkt/stationarity-3d-example}}
   {:id "V24" :name "Hamiltonian Monte Carlo"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V24 Hamiltonian Monte Carlo -- the leapfrog integrator that simulates"
    :kind :ahof-v24-hmc
    :dir "artifacts/ahof/v24-hmc"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m6/extend-environment :defs m6/definition-ids :thms m6/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'hmc/drift-unit-3d-example
    :spec {:module 'hmc :headline 'hmc/drift-unit-3d-example}}
   {:id "D35" :name "Sparse Sampling"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D35 Sparse Sampling: the sample-complexity count of the sparse-sampling"
    :kind :ahof-d35-sparse-sampling
    :dir "artifacts/ahof/d35-sparse-sampling"
    :modules [{:extend m7/extend-environment :defs m7/definition-ids :thms m7/theorem-ids}
              {:extend m8/extend-environment :defs m8/definition-ids :thms m8/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'sparse-sampling/node-count-deep-example
    :spec {:module 'sparse-sampling :headline 'sparse-sampling/node-count-deep-example}}
   {:id "O25" :name "Hypergradient Descent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O25 Hypergradient Descent: the meta-optimizer that tunes its own"
    :kind :ahof-o25-hypergrad
    :dir "artifacts/ahof/o25-hypergrad"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m9/extend-environment :defs m9/definition-ids :thms m9/theorem-ids}
              {:extend m10/extend-environment :defs m10/definition-ids :thms m10/theorem-ids}
              {:extend m11/extend-environment :defs m11/definition-ids :thms m11/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'hypergrad/orthogonal-example
    :spec {:module 'hypergrad :headline 'hypergrad/orthogonal-example}}
   {:id "V57" :name "Counterfactual Explanation"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V57 Counterfactual Explanation: the proximity term of the counterfactual"
    :kind :ahof-v57-counterfactual
    :dir "artifacts/ahof/v57-counterfactual"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}
              {:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}
              {:extend m9/extend-environment :defs m9/definition-ids :thms m9/theorem-ids}
              {:extend m10/extend-environment :defs m10/definition-ids :thms m10/theorem-ids}
              {:extend m12/extend-environment :defs m12/definition-ids :thms m12/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'counterfactual/closer-example
    :spec {:module 'counterfactual :headline 'counterfactual/closer-example}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
