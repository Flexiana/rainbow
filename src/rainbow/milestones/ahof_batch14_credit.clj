(ns rainbow.milestones.ahof-batch14-credit
  "Fourteenth batch: six fresh native proofs -- V19 MCTS for Falsification,
  O62 Gaussian Process, D53 Actor-Critic, V29 Cross-Entropy IS, O57 DCP,
  V33 Forward Reachability."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.mcts-falsification :as mcts]
            [rainbow.algorithms.proofs.ahof.gaussian-process :as gp]
            [rainbow.algorithms.proofs.ahof.actor-critic :as ac]
            [rainbow.algorithms.proofs.ahof.cross-entropy-is :as ce]
            [rainbow.algorithms.proofs.ahof.dcp :as dcp]
            [rainbow.algorithms.proofs.ahof.forward-reachability :as fr]))

(def configs
  [{:id "V19" :name "MCTS for Falsification"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Monte Carlo tree search over behaviours to find a spec violation; select children by UCB and keep the higher-scoring child."
    :kind :ahof-v19-mcts-falsification
    :dir "artifacts/ahof/v19-mcts-falsification"
    :modules [{:extend mcts/extend-environment :defs mcts/definition-ids :thms mcts/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the tree-value max"}]
    :package 'mcts-fal/tree-value-is-maximum
    :claim-boundaries {:exact-rational-only true :tree-value-max :proved :ucb-selection :proved
                       :rollout-policy :not-claimed :backpropagation :not-claimed}
    :spec {:module 'mcts-fal :headline 'mcts-fal/tree-value}}
   {:id "O62" :name "Gaussian Process"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "GP surrogate: the posterior mean at a query is a kernel-weighted combination of the observed targets."
    :kind :ahof-o62-gaussian-process
    :dir "artifacts/ahof/o62-gaussian-process"
    :modules [{:extend gp/extend-environment :defs gp/definition-ids :thms gp/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'gp/gaussian-process
    :claim-boundaries {:exact-rational-only true :kernel-weighted-mean :proved :colocated-recovery :proved
                       :covariance-kernel :not-claimed :posterior-variance :not-claimed}
    :spec {:module 'gp :headline 'gp/posterior-mean}}
   {:id "D53" :name "Actor-Critic"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "The critic bootstraps a TD target = reward + discount * next-value, toward which the actor is updated."
    :kind :ahof-d53-actor-critic
    :dir "artifacts/ahof/d53-actor-critic"
    :modules [{:extend ac/extend-environment :defs ac/definition-ids :thms ac/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'actor-critic/actor-critic
    :claim-boundaries {:exact-rational-only true :td-target-bootstrap :proved :discount-weighting :proved
                       :advantage-baseline :not-claimed :policy-gradient-step :not-claimed}
    :spec {:module 'actor-critic :headline 'actor-critic/td-target}}
   {:id "V29" :name "Cross-Entropy IS"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Cross-Entropy importance sampling fits the sampling distribution to the failure region by keeping elite samples below the cost quantile threshold."
    :kind :ahof-v29-cross-entropy-is
    :dir "artifacts/ahof/v29-cross-entropy-is"
    :modules [{:extend ce/extend-environment :defs ce/definition-ids :thms ce/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the elite certificate"}]
    :package 'ce-is/low-cost-is-elite
    :claim-boundaries {:exact-rational-only true :elite-threshold-decision :proved :elite-certificate :proved
                       :distribution-fitting :not-claimed :quantile-estimation :not-claimed}
    :spec {:module 'ce-is :headline 'ce-is/elite?}}
   {:id "O57" :name "Disciplined Convex Programming"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "DCP builds convex programs from convex atoms so feasibility of each convex constraint g(x) <= b reduces to a decidable exact-rational comparison."
    :kind :ahof-o57-dcp
    :dir "artifacts/ahof/o57-dcp"
    :modules [{:extend dcp/extend-environment :defs dcp/definition-ids :thms dcp/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the feasibility certificate"}]
    :package 'dcp/feasible-point
    :claim-boundaries {:exact-rational-only true :convex-constraint-feasibility :proved :feasibility-certificate :proved
                       :curvature-atom-grammar :not-claimed :cone-solver :not-claimed}
    :spec {:module 'dcp :headline 'dcp/constraint-satisfied?}}
   {:id "V33" :name "Forward Reachability"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Over-approximate the reachable set by forward-propagating an enclosure; a state is in the over-approximation when its distance to the representative is within the enclosure radius."
    :kind :ahof-v33-forward-reachability
    :dir "artifacts/ahof/v33-forward-reachability"
    :modules [{:extend fr/extend-environment :defs fr/definition-ids :thms fr/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the reach certificate"}]
    :package 'forward-reach/within-enclosure-reachable
    :claim-boundaries {:exact-rational-only true :enclosure-membership-decision :proved :reach-certificate :proved
                       :set-propagation-operator :not-claimed :fixpoint-termination :not-claimed}
    :spec {:module 'forward-reach :headline 'forward-reach/in-reachable-set?}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
