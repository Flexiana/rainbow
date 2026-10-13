(ns rainbow.milestones.ahof-batch8-credit
  "Eighth batch: three fresh native proofs -- D24 LP Formulation of MDP,
  D77 Nash Equilibrium, O69 Uncertainty Propagation (MC mean)."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.lp-mdp :as lp]
            [rainbow.algorithms.proofs.ahof.nash-equilibrium :as nash]
            [rainbow.algorithms.proofs.ahof.mc-mean :as mc]))

(def configs
  [{:id "D24" :name "LP Formulation of MDP"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "The optimal value function solves an LP that minimizes total value subject to Bellman inequality constraints V(s) >= backup for every state-action pair."
    :kind :ahof-d24-lp-mdp
    :dir "artifacts/ahof/d24-lp-mdp"
    :modules [{:extend lp/extend-environment :defs lp/definition-ids :thms lp/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the feasibility certificate"}]
    :package 'lp-mdp/feasible-value
    :claim-boundaries {:exact-rational-only true :bellman-inequality-constraint :proved :feasibility-certificate :proved
                       :lp-objective-optimization :not-claimed :dual-complementarity :not-claimed}
    :spec {:module 'lp-mdp :headline 'lp-mdp/satisfies-bellman?}}
   {:id "D77" :name "Nash Equilibrium (Support Enum)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "A profile is a Nash equilibrium when no player can gain by unilaterally deviating; the per-player test compares a deviation payoff against the current payoff."
    :kind :ahof-d77-nash-equilibrium
    :dir "artifacts/ahof/d77-nash-equilibrium"
    :modules [{:extend nash/extend-environment :defs nash/definition-ids :thms nash/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the stability certificate"}]
    :package 'nash/stable-profile
    :claim-boundaries {:exact-rational-only true :no-profitable-deviation-decision :proved :stability-certificate :proved
                       :mixed-strategy-support-enumeration :not-claimed :existence-theorem :not-claimed}
    :spec {:module 'nash :headline 'nash/no-profitable-deviation?}}
   {:id "O69" :name "Uncertainty Propagation (MC)"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Propagate input uncertainty by sampling and averaging the outputs; the two-sample Monte Carlo mean weights each sample equally."
    :kind :ahof-o69-mc-mean
    :dir "artifacts/ahof/o69-mc-mean"
    :modules [{:extend mc/extend-environment :defs mc/definition-ids :thms mc/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'mc-mean/mc-mean
    :claim-boundaries {:exact-rational-only true :monte-carlo-mean-estimator :proved :equal-sample-weighting :proved
                       :variance-estimate :not-claimed :confidence-interval :not-claimed}
    :spec {:module 'mc-mean :headline 'mc-mean/estimate}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
