(ns rainbow.milestones.ahof-batch2-credit
  "Second batch: pending AHoF rows whose native proofs live in non-ahof-prefixed
  id-tagged logic modules."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.adadelta :as m0]
            [rainbow.algorithms.proofs.adam :as m1]
            [rainbow.algorithms.proofs.adaptive-gradient :as m2]
            [rainbow.algorithms.proofs.admm :as m3]
            [rainbow.algorithms.proofs.augmented-lagrangian :as m4]
            [rainbow.algorithms.proofs.counterfactual :as m5]
            [rainbow.algorithms.proofs.cuckoo-search :as m6]
            [rainbow.algorithms.proofs.differential-evolution :as m7]
            [rainbow.algorithms.proofs.dual-ascent :as m8]
            [rainbow.algorithms.proofs.feature-importance :as m9]
            [rainbow.algorithms.proofs.firefly :as m10]
            [rainbow.algorithms.proofs.full-factorial :as m11]
            [rainbow.algorithms.proofs.hooke-jeeves :as m12]
            [rainbow.algorithms.proofs.hypergradient :as m13]
            [rainbow.algorithms.proofs.interior-point :as m14]
            [rainbow.algorithms.proofs.latin-hypercube :as m15]
            [rainbow.algorithms.proofs.metropolis :as m16]
            [rainbow.algorithms.proofs.nelder-mead :as m17]
            [rainbow.algorithms.proofs.noisy-descent :as m18]
            [rainbow.algorithms.proofs.particle-swarm :as m19]
            [rainbow.algorithms.proofs.powell :as m20]
            [rainbow.algorithms.proofs.reward-to-go :as m21]
            [rainbow.algorithms.proofs.rmsprop :as m22]
            [rainbow.algorithms.proofs.sparse-sampling :as m23]
            [rainbow.algorithms.proofs.tournament-selection :as m24]))

(def configs
  [
   {:id "O23" :name "Adadelta"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O23 Adadelta: the learning-rate-free update scale. Adadelta needs no"
    :kind :ahof-o23-adadelta
    :dir "artifacts/ahof/o23-adadelta"
    :modules [{:extend m0/extend-environment :defs m0/definition-ids :thms m0/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/divide :statement "shared exact-rational prerequisite is present"}]
    :package 'adadelta/scale-above-one-example
    :spec {:module 'adadelta :headline 'adadelta/scale-above-one-example}}
   {:id "O24" :name "Adam"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O24 Adam: the first-moment (momentum) estimate and the preconditioned"
    :kind :ahof-o24-adam
    :dir "artifacts/ahof/o24-adam"
    :modules [{:extend m1/extend-environment :defs m1/definition-ids :thms m1/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'adam/direction-example
    :spec {:module 'adam :headline 'adam/direction-example}}
   {:id "O21" :name "AdaGrad"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O21 AdaGrad: the adaptive per-parameter learning rate. AdaGrad divides a"
    :kind :ahof-o21-adagrad
    :dir "artifacts/ahof/o21-adagrad"
    :modules [{:extend m2/extend-environment :defs m2/definition-ids :thms m2/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/divide :statement "shared exact-rational prerequisite is present"}]
    :package 'adagrad/adaptive-rate-example
    :spec {:module 'adagrad :headline 'adagrad/adaptive-rate-example}}
   {:id "O51" :name "ADMM"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O51 ADMM (Alternating Direction Method of Multipliers): the scaled-form"
    :kind :ahof-o51-admm
    :dir "artifacts/ahof/o51-admm"
    :modules [{:extend m3/extend-environment :defs m3/definition-ids :thms m3/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'admm/residual-3d-example
    :spec {:module 'admm :headline 'admm/residual-3d-example}}
   {:id "O49" :name "Augmented Lagrangian"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O49 Augmented Lagrangian: the dual multiplier update in the outer loop."
    :kind :ahof-o49-lagrangian
    :dir "artifacts/ahof/o49-lagrangian"
    :modules [{:extend m4/extend-environment :defs m4/definition-ids :thms m4/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/add :statement "shared exact-rational prerequisite is present"}]
    :package 'lagrangian/over-satisfied-example
    :spec {:module 'lagrangian :headline 'lagrangian/over-satisfied-example}}
   {:id "V57" :name "Counterfactual Explanation"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V57 Counterfactual Explanation: the proximity term of the counterfactual"
    :kind :ahof-v57-counterfactual
    :dir "artifacts/ahof/v57-counterfactual"
    :modules [{:extend m5/extend-environment :defs m5/definition-ids :thms m5/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'counterfactual/closer-example
    :spec {:module 'counterfactual :headline 'counterfactual/closer-example}}
   {:id "O47" :name "Cuckoo Search"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O47 Cuckoo Search: the Levy-flight step over vector-valued state. A"
    :kind :ahof-o47-cuckoo
    :dir "artifacts/ahof/o47-cuckoo"
    :modules [{:extend m6/extend-environment :defs m6/definition-ids :thms m6/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'cuckoo/scaled-flight-example
    :spec {:module 'cuckoo :headline 'cuckoo/scaled-flight-example}}
   {:id "O44" :name "Differential Evolution"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O44 Differential Evolution: the differential mutation over vector-valued"
    :kind :ahof-o44-evolution
    :dir "artifacts/ahof/o44-evolution"
    :modules [{:extend m7/extend-environment :defs m7/definition-ids :thms m7/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'evolution/unit-mutation-example
    :spec {:module 'evolution :headline 'evolution/unit-mutation-example}}
   {:id "O52" :name "Dual Ascent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O52 Dual Ascent: the dual-variable ascent step over vector-valued"
    :kind :ahof-o52-dual-ascent
    :dir "artifacts/ahof/o52-dual-ascent"
    :modules [{:extend m8/extend-environment :defs m8/definition-ids :thms m8/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'dual-ascent/unit-step-3d-example
    :spec {:module 'dual-ascent :headline 'dual-ascent/unit-step-3d-example}}
   {:id "V54" :name "Permutation Feature Importance"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V54 Permutation Feature Importance: the drop in model score when a"
    :kind :ahof-v54-importance
    :dir "artifacts/ahof/v54-importance"
    :modules [{:extend m9/extend-environment :defs m9/definition-ids :thms m9/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'importance/unused-example
    :spec {:module 'importance :headline 'importance/unused-example}}
   {:id "O46" :name "Firefly Algorithm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O46 Firefly Algorithm: the attraction move over vector-valued state. A"
    :kind :ahof-o46-firefly
    :dir "artifacts/ahof/o46-firefly"
    :modules [{:extend m10/extend-environment :defs m10/definition-ids :thms m10/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'firefly/full-attraction-3d-example
    :spec {:module 'firefly :headline 'firefly/full-attraction-3d-example}}
   {:id "O58" :name "Full Factorial Sampling"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O58 Full Factorial Sampling: the design size is the product of the"
    :kind :ahof-o58-full-factorial
    :dir "artifacts/ahof/o58-full-factorial"
    :modules [{:extend m11/extend-environment :defs m11/definition-ids :thms m11/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'full-factorial/design-size-empty-example
    :spec {:module 'full-factorial :headline 'full-factorial/design-size-empty-example}}
   {:id "O34" :name "Hooke-Jeeves"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O34 Hooke-Jeeves pattern search: the exploratory probe and the pattern"
    :kind :ahof-o34-hooke
    :dir "artifacts/ahof/o34-hooke"
    :modules [{:extend m12/extend-environment :defs m12/definition-ids :thms m12/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'hooke/pattern-move-3d-example
    :spec {:module 'hooke :headline 'hooke/pattern-move-3d-example}}
   {:id "O25" :name "Hypergradient Descent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O25 Hypergradient Descent: the meta-optimizer that tunes its own"
    :kind :ahof-o25-hypergrad
    :dir "artifacts/ahof/o25-hypergrad"
    :modules [{:extend m13/extend-environment :defs m13/definition-ids :thms m13/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/add :statement "shared exact-rational prerequisite is present"}]
    :package 'hypergrad/orthogonal-example
    :spec {:module 'hypergrad :headline 'hypergrad/orthogonal-example}}
   {:id "O50" :name "Interior Point / Barrier"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O50 Interior Point / Barrier Method: the transform that keeps iterates"
    :kind :ahof-o50-barrier
    :dir "artifacts/ahof/o50-barrier"
    :modules [{:extend m14/extend-environment :defs m14/definition-ids :thms m14/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/divide :statement "shared exact-rational prerequisite is present"}]
    :package 'barrier/wide-slack-example
    :spec {:module 'barrier :headline 'barrier/wide-slack-example}}
   {:id "O59" :name "Latin Hypercube Sampling"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O59 Latin Hypercube Sampling: a space-filling design that draws exactly"
    :kind :ahof-o59-latin-hypercube
    :dir "artifacts/ahof/o59-latin-hypercube"
    :modules [{:extend m15/extend-environment :defs m15/definition-ids :thms m15/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'latin-hypercube/total-strata-4x3-example
    :spec {:module 'latin-hypercube :headline 'latin-hypercube/total-strata-4x3-example}}
   {:id "V22" :name "Metropolis-Hastings MCMC"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "AHoF V22 Metropolis-Hastings acceptance (also the acceptance rule of"
    :kind :ahof-v22-metropolis
    :dir "artifacts/ahof/v22-metropolis"
    :modules [{:extend m16/extend-environment :defs m16/definition-ids :thms m16/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'metropolis/uphill-not-deterministic
    :spec {:module 'metropolis :headline 'metropolis/uphill-not-deterministic}}
   {:id "O36" :name "Nelder-Mead Simplex"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O36 Nelder-Mead Simplex: the reflection move, the workhorse simplex"
    :kind :ahof-o36-nelder
    :dir "artifacts/ahof/o36-nelder"
    :modules [{:extend m17/extend-environment :defs m17/definition-ids :thms m17/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'signed/add :statement "shared exact-rational prerequisite is present"}]
    :package 'nelder/reflect-example
    :spec {:module 'nelder :headline 'nelder/reflect-example}}
   {:id "O38" :name "Noisy Descent"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O38 Noisy Descent: the WRAP pattern that perturbs a base descent step"
    :kind :ahof-o38-noisy
    :dir "artifacts/ahof/o38-noisy"
    :modules [{:extend m18/extend-environment :defs m18/definition-ids :thms m18/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'noisy/wrap-3d-example
    :spec {:module 'noisy :headline 'noisy/wrap-3d-example}}
   {:id "O45" :name "Particle Swarm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O45 Particle Swarm Optimization: the per-particle velocity and position"
    :kind :ahof-o45-swarm
    :dir "artifacts/ahof/o45-swarm"
    :modules [{:extend m19/extend-environment :defs m19/definition-ids :thms m19/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'swarm/step-example
    :spec {:module 'swarm :headline 'swarm/step-example}}
   {:id "O33" :name "Powell's Method"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O33 Powell's Method: the conjugate search-direction generated from a"
    :kind :ahof-o33-powell
    :dir "artifacts/ahof/o33-powell"
    :modules [{:extend m20/extend-environment :defs m20/definition-ids :thms m20/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}]
    :package 'powell/net-direction-3d-example
    :spec {:module 'powell :headline 'powell/net-direction-3d-example}}
   {:id "D47" :name "Reward-to-Go"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D47 Reward-to-Go: the future-reward sum used by policy-gradient methods"
    :kind :ahof-d47-reward-to-go
    :dir "artifacts/ahof/d47-reward-to-go"
    :modules [{:extend m21/extend-environment :defs m21/definition-ids :thms m21/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'reward-to-go/empty-return-example
    :spec {:module 'reward-to-go :headline 'reward-to-go/empty-return-example}}
   {:id "O22" :name "RMSProp"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O22 RMSProp: the decayed squared-gradient accumulator that adapts the"
    :kind :ahof-o22-rmsprop
    :dir "artifacts/ahof/o22-rmsprop"
    :modules [{:extend m22/extend-environment :defs m22/definition-ids :thms m22/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/multiply :statement "shared exact-rational prerequisite is present"}]
    :package 'rmsprop/rising-example
    :spec {:module 'rmsprop :headline 'rmsprop/rising-example}}
   {:id "D35" :name "Sparse Sampling"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "AHoF D35 Sparse Sampling: the sample-complexity count of the sparse-sampling"
    :kind :ahof-d35-sparse-sampling
    :dir "artifacts/ahof/d35-sparse-sampling"
    :modules [{:extend m23/extend-environment :defs m23/definition-ids :thms m23/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/make :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/add :statement "shared exact-rational prerequisite is present"}]
    :package 'sparse-sampling/node-count-deep-example
    :spec {:module 'sparse-sampling :headline 'sparse-sampling/node-count-deep-example}}
   {:id "O43" :name "Genetic Algorithm"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "AHoF O43 Genetic Algorithm -- tournament selection operator: from a sampled"
    :kind :ahof-o43-tournament
    :dir "artifacts/ahof/o43-tournament"
    :modules [{:extend m24/extend-environment :defs m24/definition-ids :thms m24/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "shared exact-rational prerequisite is present"}
                       {:target/name 'nnrat/at-most :statement "shared exact-rational prerequisite is present"}]
    :package 'tournament/winner-dominates-entrant
    :spec {:module 'tournament :headline 'tournament/winner-dominates-entrant}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
