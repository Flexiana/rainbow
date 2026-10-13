(ns rainbow.milestones.ahof-batch15-credit
  "Fifteenth batch: eight fresh native proofs -- V34 Polytope Propagation,
  V41 Natural Inclusion Function, D54 GAE, O70 Genetic Programming,
  D81 Nash Q-Learning, V20 RL for Falsification, V47 NN Verification,
  V51 Probabilistic Reachability."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.polytope :as poly]
            [rainbow.algorithms.proofs.ahof.natural-inclusion :as ni]
            [rainbow.algorithms.proofs.ahof.gae54 :as gae]
            [rainbow.algorithms.proofs.ahof.genetic-programming :as gp]
            [rainbow.algorithms.proofs.ahof.nash-q-learning :as nq]
            [rainbow.algorithms.proofs.ahof.rl-falsification :as rl]
            [rainbow.algorithms.proofs.ahof.nn-verification :as nn]
            [rainbow.algorithms.proofs.ahof.probabilistic-reachability :as pr]))

(defn- decide-prereqs []
  [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
   {:target/name 'logic/if-data :statement "boolean/selection eliminator is present"}])
(defn- atmost-prereqs []
  [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
   {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the certificate"}])
(defn- arith-prereqs []
  [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
   {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}])

(def configs
  [{:id "V34" :name "Polytope Propagation" :source-file "catalog/03_validation_algorithms.md"
    :listing "Represent a reachable set as an intersection of halfspaces; a point is inside when it satisfies all halfspace inequalities."
    :kind :ahof-v34-polytope :dir "artifacts/ahof/v34-polytope"
    :modules [{:extend poly/extend-environment :defs poly/definition-ids :thms poly/theorem-ids}]
    :baseline-prereqs (decide-prereqs) :package 'polytope/inside-both-halfspaces
    :claim-boundaries {:exact-rational-only true :halfspace-conjunction-membership :proved :arbitrary-facet-count :not-claimed}
    :spec {:module 'polytope :headline 'polytope/in-polytope?}}
   {:id "V41" :name "Natural Inclusion Function" :source-file "catalog/03_validation_algorithms.md"
    :listing "Interval extension gives a guaranteed enclosure of a range; a value is certified within the enclosure when it lies between the bounds."
    :kind :ahof-v41-natural-inclusion :dir "artifacts/ahof/v41-natural-inclusion"
    :modules [{:extend ni/extend-environment :defs ni/definition-ids :thms ni/theorem-ids}]
    :baseline-prereqs (decide-prereqs) :package 'nat-incl/value-enclosed
    :claim-boundaries {:exact-rational-only true :enclosure-membership :proved :tightness :not-claimed}
    :spec {:module 'nat-incl :headline 'nat-incl/encloses?}}
   {:id "D54" :name "Generalized Advantage Estimation" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Exponentially-weighted sum of one-step TD residuals; the recursive form combines the current residual with the discounted future advantage."
    :kind :ahof-d54-gae :dir "artifacts/ahof/d54-gae"
    :modules [{:extend gae/extend-environment :defs gae/definition-ids :thms gae/theorem-ids}]
    :baseline-prereqs (arith-prereqs) :package 'gae54/gae
    :claim-boundaries {:exact-rational-only true :recursive-advantage :proved :lambda-schedule :not-claimed}
    :spec {:module 'gae54 :headline 'gae54/gae-advantage}}
   {:id "O70" :name "Genetic Programming" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Evolve expression-tree programs under fitness selection; keep the fitter of two candidate programs."
    :kind :ahof-o70-genetic-programming :dir "artifacts/ahof/o70-genetic-programming"
    :modules [{:extend gp/extend-environment :defs gp/definition-ids :thms gp/theorem-ids}]
    :baseline-prereqs (decide-prereqs) :package 'gp-tree/value-is-maximum
    :claim-boundaries {:exact-rational-only true :fitness-max-selection :proved :crossover-mutation :not-claimed}
    :spec {:module 'gp-tree :headline 'gp-tree/best-fitness}}
   {:id "D81" :name "Nash Q-Learning" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Learn stage-game Q-values and back up the Nash value; the backup keeps the larger joint-action value."
    :kind :ahof-d81-nash-q-learning :dir "artifacts/ahof/d81-nash-q-learning"
    :modules [{:extend nq/extend-environment :defs nq/definition-ids :thms nq/theorem-ids}]
    :baseline-prereqs (decide-prereqs) :package 'nashq/value-is-maximum
    :claim-boundaries {:exact-rational-only true :nash-value-max :proved :equilibrium-solver :not-claimed}
    :spec {:module 'nashq :headline 'nashq/nash-value}}
   {:id "V20" :name "RL for Falsification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Train an RL agent to drive the system toward a violation, acting greedily on the learned Q-values."
    :kind :ahof-v20-rl-falsification :dir "artifacts/ahof/v20-rl-falsification"
    :modules [{:extend rl/extend-environment :defs rl/definition-ids :thms rl/theorem-ids}]
    :baseline-prereqs (decide-prereqs) :package 'rl-fal/value-is-maximum
    :claim-boundaries {:exact-rational-only true :greedy-q-max :proved :exploration-schedule :not-claimed}
    :spec {:module 'rl-fal :headline 'rl-fal/best-q}}
   {:id "V47" :name "Neural Network Verification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Certify that a network's output stays within a safety bound over an input region; a concrete output is safe when within the bound."
    :kind :ahof-v47-nn-verification :dir "artifacts/ahof/v47-nn-verification"
    :modules [{:extend nn/extend-environment :defs nn/definition-ids :thms nn/theorem-ids}]
    :baseline-prereqs (atmost-prereqs) :package 'nnverify/output-within-bound-safe
    :claim-boundaries {:exact-rational-only true :safety-bound-decision :proved :bound-propagation :not-claimed}
    :spec {:module 'nnverify :headline 'nnverify/safe?}}
   {:id "V51" :name "Probabilistic Reachability" :source-file "catalog/03_validation_algorithms.md"
    :listing "Compute the probability of reaching a target set and flag it likely-reachable when that probability meets a confidence threshold."
    :kind :ahof-v51-probabilistic-reachability :dir "artifacts/ahof/v51-probabilistic-reachability"
    :modules [{:extend pr/extend-environment :defs pr/definition-ids :thms pr/theorem-ids}]
    :baseline-prereqs (atmost-prereqs) :package 'prob-reach/high-probability-likely
    :claim-boundaries {:exact-rational-only true :probability-threshold-decision :proved :probability-computation :not-claimed}
    :spec {:module 'prob-reach :headline 'prob-reach/likely-reachable?}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
