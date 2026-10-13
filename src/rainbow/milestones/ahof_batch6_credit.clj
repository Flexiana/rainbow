(ns rainbow.milestones.ahof-batch6-credit
  "Sixth batch: three fresh native proofs -- O67 Epsilon-Constraint,
  D57 UCB1, O66 Weighted Sum Method."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.epsilon-constraint :as ec]
            [rainbow.algorithms.proofs.ahof.ucb1 :as ucb]
            [rainbow.algorithms.proofs.ahof.weighted-sum :as ws]))

(def configs
  [{:id "O67" :name "Epsilon-Constraint"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Multi-objective: optimize one objective while the others become inequality constraints f_i <= epsilon_i; feasibility is the threshold decision value <= epsilon."
    :kind :ahof-o67-epsilon-constraint
    :dir "artifacts/ahof/o67-epsilon-constraint"
    :modules [{:extend ec/extend-environment :defs ec/definition-ids :thms ec/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the feasibility certificate"}]
    :package 'epsilon-constraint/within-bound-feasible
    :claim-boundaries {:exact-rational-only true :feasibility-threshold-decision :proved
                       :scalar-objective-optimization :not-claimed :epsilon-schedule :not-claimed}
    :spec {:module 'epsilon-constraint :headline 'epsilon-constraint/feasible?}}
   {:id "D57" :name "UCB1 (Bandits)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Bandit arm selection: pull the arm with the largest upper-confidence-bound score; the policy keeps the larger score and prefers arm 0 when its UCB is at least arm 1's."
    :kind :ahof-d57-ucb1
    :dir "artifacts/ahof/d57-ucb1"
    :modules [{:extend ucb/extend-environment :defs ucb/definition-ids :thms ucb/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the max selection"}]
    :package 'ucb1/selects-higher-value
    :claim-boundaries {:exact-rational-only true :largest-score-selection :proved :preference-decision :proved
                       :confidence-bonus-formula :not-claimed :regret-bound :not-claimed}
    :spec {:module 'ucb1 :headline 'ucb1/best-score}}
   {:id "O66" :name "Weighted Sum Method"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "Multi-objective scalarization: collapse objectives into one scalar by a weighted sum w1*f1 + w2*f2, then optimize the scalar."
    :kind :ahof-o66-weighted-sum
    :dir "artifacts/ahof/o66-weighted-sum"
    :modules [{:extend ws/extend-environment :defs ws/definition-ids :thms ws/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
                       {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}]
    :package 'weighted-sum/weighted-sum
    :claim-boundaries {:exact-rational-only true :weighted-scalarization :proved :weights-steer-aggregate :proved
                       :arbitrary-objective-count :not-claimed :pareto-completeness :not-claimed}
    :spec {:module 'weighted-sum :headline 'weighted-sum/scalarize}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
