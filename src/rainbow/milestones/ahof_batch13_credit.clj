(ns rainbow.milestones.ahof-batch13-credit
  "Thirteenth batch: five fresh native proofs -- V18 A* for Falsification,
  V27 Importance Sampling, D75 POMCP, D65 DAgger, O60 Sobol Sequences."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.astar-falsification :as astar]
            [rainbow.algorithms.proofs.ahof.is-falsification :as is]
            [rainbow.algorithms.proofs.ahof.pomcp :as pomcp]
            [rainbow.algorithms.proofs.ahof.dagger :as dagger]
            [rainbow.algorithms.proofs.ahof.sobol :as sobol]))

(def configs
  [{:id "V18" :name "A* for Falsification"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Search behaviours for a specification violation with A*, ordering the frontier by f = g + h and expanding the lowest-f node."
    :kind :ahof-v18-astar-falsification
    :dir "artifacts/ahof/v18-astar-falsification"
    :modules [{:extend astar/extend-environment :defs astar/definition-ids :thms astar/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present for the f-cost"}
                       {:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}]
    :package 'astar-fal/priority-is-three-quarters
    :claim-boundaries {:exact-rational-only true :f-cost-sum :proved :min-frontier-selection :proved
                       :heuristic-admissibility :not-claimed :optimality-proof :not-claimed}
    :spec {:module 'astar-fal :headline 'astar-fal/priority}}
   {:id "V27" :name "Importance Sampling"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Estimate a rare-failure probability by sampling from a proposal and reweighting by the importance weight, the ratio of target to proposal density."
    :kind :ahof-v27-is-falsification
    :dir "artifacts/ahof/v27-is-falsification"
    :modules [{:extend is/extend-environment :defs is/definition-ids :thms is/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/divide :statement "exact-rational division is present for the importance ratio"}
                       {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present for the weights"}]
    :package 'is-weight/rare-event-weight-is-two
    :claim-boundaries {:exact-rational-only true :importance-ratio :proved :weight-values :proved
                       :variance-minimizing-proposal :not-claimed :effective-sample-size :not-claimed}
    :spec {:module 'is-weight :headline 'is-weight/importance-weight}}
   {:id "D75" :name "Online POMDP (POMCP)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Monte Carlo tree search in belief space; select actions by UCB score and keep the higher-scoring action as the node value."
    :kind :ahof-d75-pomcp
    :dir "artifacts/ahof/d75-pomcp"
    :modules [{:extend pomcp/extend-environment :defs pomcp/definition-ids :thms pomcp/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the node-value max"}]
    :package 'pomcp/node-value-is-maximum
    :claim-boundaries {:exact-rational-only true :node-value-max :proved :ucb-preference :proved
                       :rollout-simulation :not-claimed :belief-particle-set :not-claimed}
    :spec {:module 'pomcp :headline 'pomcp/node-value}}
   {:id "D65" :name "DAgger"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Dataset Aggregation: run the current policy, query the expert to label visited states, aggregate; query the expert when policy uncertainty reaches a threshold."
    :kind :ahof-d65-dagger
    :dir "artifacts/ahof/d65-dagger"
    :modules [{:extend dagger/extend-environment :defs dagger/definition-ids :thms dagger/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the query certificate"}]
    :package 'dagger/high-uncertainty-queries
    :claim-boundaries {:exact-rational-only true :uncertainty-threshold-decision :proved :query-certificate :proved
                       :dataset-aggregation :not-claimed :no-regret-guarantee :not-claimed}
    :spec {:module 'dagger :headline 'dagger/query-expert?}}
   {:id "O60" :name "Sobol Sequences"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Quasi-random low-discrepancy sequence for uniform space-filling sampling; meets its uniformity target when the star discrepancy stays within the bound."
    :kind :ahof-o60-sobol
    :dir "artifacts/ahof/o60-sobol"
    :modules [{:extend sobol/extend-environment :defs sobol/definition-ids :thms sobol/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the discrepancy certificate"}]
    :package 'sobol/within-bound-uniform
    :claim-boundaries {:exact-rational-only true :discrepancy-bound-decision :proved :discrepancy-certificate :proved
                       :direction-number-construction :not-claimed :sequence-generation :not-claimed}
    :spec {:module 'sobol :headline 'sobol/low-discrepancy?}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
