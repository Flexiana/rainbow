(ns rainbow.milestones.ahof-batch12-credit
  "Twelfth batch: five fresh native proofs -- D74 SARSOP, V8 Reachability
  Specification, D78 Correlated Equilibrium, D72 PBVI, D69 UKF."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.sarsop :as sarsop]
            [rainbow.algorithms.proofs.ahof.reachability-spec :as reach]
            [rainbow.algorithms.proofs.ahof.correlated-equilibrium :as corr]
            [rainbow.algorithms.proofs.ahof.pbvi :as pbvi]
            [rainbow.algorithms.proofs.ahof.ukf :as ukf]))

(def configs
  [{:id "D74" :name "SARSOP"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Point-based POMDP solver that samples beliefs reachable under the optimal policy; converged when the value-bound gap is within precision."
    :kind :ahof-d74-sarsop
    :dir "artifacts/ahof/d74-sarsop"
    :modules [{:extend sarsop/extend-environment :defs sarsop/definition-ids :thms sarsop/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the gap certificate"}]
    :package 'sarsop/small-gap-converged
    :claim-boundaries {:exact-rational-only true :bound-gap-convergence :proved :gap-certificate :proved
                       :reachable-belief-sampling :not-claimed}
    :spec {:module 'sarsop :headline 'sarsop/converged?}}
   {:id "V8" :name "Reachability Specification"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "A reachability property asks whether the system can reach a target set; a trajectory reaches it when its distance to the target is within the specification tolerance."
    :kind :ahof-v8-reachability-spec
    :dir "artifacts/ahof/v8-reachability-spec"
    :modules [{:extend reach/extend-environment :defs reach/definition-ids :thms reach/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the reach certificate"}]
    :package 'reach-spec/within-tolerance-reaches
    :claim-boundaries {:exact-rational-only true :target-tolerance-decision :proved :reach-certificate :proved
                       :temporal-reachability-operators :not-claimed}
    :spec {:module 'reach-spec :headline 'reach-spec/reaches-target?}}
   {:id "D78" :name "Correlated Equilibrium"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "A distribution over joint action profiles from which no player gains by deviating from the mediator's recommendation; the adherence test compares deviation vs recommended payoff."
    :kind :ahof-d78-correlated-equilibrium
    :dir "artifacts/ahof/d78-correlated-equilibrium"
    :modules [{:extend corr/extend-environment :defs corr/definition-ids :thms corr/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the adherence certificate"}]
    :package 'correlated/adheres-to-recommendation
    :claim-boundaries {:exact-rational-only true :adherence-decision :proved :adherence-certificate :proved
                       :mediator-distribution :not-claimed :linear-program-formulation :not-claimed}
    :spec {:module 'correlated :headline 'correlated/follows-recommendation?}}
   {:id "D72" :name "PBVI (Point-Based)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Point-Based Value Iteration for POMDPs: back up value at a finite set of belief points as the maximum over candidate alpha vectors."
    :kind :ahof-d72-pbvi
    :dir "artifacts/ahof/d72-pbvi"
    :modules [{:extend pbvi/extend-environment :defs pbvi/definition-ids :thms pbvi/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the backup max"}]
    :package 'pbvi/backup-is-maximum
    :claim-boundaries {:exact-rational-only true :backup-maximum :proved :preference-decision :proved
                       :belief-point-set-selection :not-claimed}
    :spec {:module 'pbvi :headline 'pbvi/backup-value}}
   {:id "D69" :name "Unscented Kalman Filter"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Propagate deterministically chosen sigma points through the nonlinear model and recover the posterior mean as their weighted average."
    :kind :ahof-d69-ukf
    :dir "artifacts/ahof/d69-ukf"
    :modules [{:extend ukf/extend-environment :defs ukf/definition-ids :thms ukf/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'ukf/ukf
    :claim-boundaries {:exact-rational-only true :sigma-point-weighted-mean :proved :weighting :proved
                       :sigma-point-selection :not-claimed :covariance-recovery :not-claimed}
    :spec {:module 'ukf :headline 'ukf/sigma-mean}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
