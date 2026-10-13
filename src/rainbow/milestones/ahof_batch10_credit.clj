(ns rainbow.milestones.ahof-batch10-credit
  "Tenth batch: four fresh native proofs -- D64 Behavioral Cloning,
  O73 Cutting Planes, D79 Fictitious Play, D68 Extended Kalman Filter."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.behavioral-cloning :as bc]
            [rainbow.algorithms.proofs.ahof.cutting-planes :as cp]
            [rainbow.algorithms.proofs.ahof.fictitious-play :as fp]
            [rainbow.algorithms.proofs.ahof.ekf :as ekf]))

(def configs
  [{:id "D64" :name "Behavioral Cloning"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Imitation learning by supervised matching of an expert's actions; the clone is accepted on a demonstration when its imitation loss is within tolerance."
    :kind :ahof-d64-behavioral-cloning
    :dir "artifacts/ahof/d64-behavioral-cloning"
    :modules [{:extend bc/extend-environment :defs bc/definition-ids :thms bc/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the acceptance certificate"}]
    :package 'cloning/perfect-match-accepted
    :claim-boundaries {:exact-rational-only true :loss-tolerance-decision :proved :acceptance-certificate :proved
                       :distribution-shift :not-claimed :expert-optimality :not-claimed}
    :spec {:module 'cloning :headline 'cloning/within-tolerance?}}
   {:id "O73" :name "Cutting Planes"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Add linear inequalities (cuts) that remove the current infeasible LP point while preserving all true solutions; a cut is added exactly when the point violates a constraint."
    :kind :ahof-o73-cutting-planes
    :dir "artifacts/ahof/o73-cutting-planes"
    :modules [{:extend cp/extend-environment :defs cp/definition-ids :thms cp/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the add-cut negation"}]
    :package 'cutting-planes/violated-cut-added
    :claim-boundaries {:exact-rational-only true :feasibility-decision :proved :add-cut-complement :proved
                       :cut-generation-formula :not-claimed :convergence :not-claimed}
    :spec {:module 'cutting-planes :headline 'cutting-planes/feasible?}}
   {:id "D79" :name "Fictitious Play"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Each player best-responds to the empirical frequency of the opponent's past actions; the best response keeps the higher expected payoff."
    :kind :ahof-d79-fictitious-play
    :dir "artifacts/ahof/d79-fictitious-play"
    :modules [{:extend fp/extend-environment :defs fp/definition-ids :thms fp/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the best-response max"}]
    :package 'fictitious/best-response-is-larger
    :claim-boundaries {:exact-rational-only true :best-response-max :proved :preference-decision :proved
                       :empirical-frequency-update :not-claimed :convergence-to-equilibrium :not-claimed}
    :spec {:module 'fictitious :headline 'fictitious/best-response-value}}
   {:id "D68" :name "Extended Kalman Filter"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Linearize the nonlinear models about the current estimate and apply the Kalman measurement update, blending prediction and observation by the Kalman gain."
    :kind :ahof-d68-ekf
    :dir "artifacts/ahof/d68-ekf"
    :modules [{:extend ekf/extend-environment :defs ekf/definition-ids :thms ekf/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'ekf/ekf
    :claim-boundaries {:exact-rational-only true :measurement-update-blend :proved :gain-weighting :proved
                       :jacobian-linearization :not-claimed :covariance-propagation :not-claimed}
    :spec {:module 'ekf :headline 'ekf/update}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
