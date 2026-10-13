(ns rainbow.milestones.ahof-batch19-credit
  "Nineteenth batch: fourteen fresh native proofs -- O11 D38 V17 D44 D56 D76
  D39 D83 V3 V10 V23 D1 V25 V30."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.shubert :as sh]
            [rainbow.algorithms.proofs.ahof.lao-star :as lao]
            [rainbow.algorithms.proofs.ahof.tree-search-fal :as tf]
            [rainbow.algorithms.proofs.ahof.isotropic-es :as ies]
            [rainbow.algorithms.proofs.ahof.ac-mcts :as acm]
            [rainbow.algorithms.proofs.ahof.finite-state-controller :as fsc]
            [rainbow.algorithms.proofs.ahof.open-loop-planning :as olp]
            [rainbow.algorithms.proofs.ahof.dec-pomdp-hs :as dhs]
            [rainbow.algorithms.proofs.ahof.agent-model :as am]
            [rainbow.algorithms.proofs.ahof.disturbance-falsification :as df]
            [rainbow.algorithms.proofs.ahof.gibbs-failures :as gf]
            [rainbow.algorithms.proofs.ahof.bayes-net :as bn]
            [rainbow.algorithms.proofs.ahof.prob-programming :as pp]
            [rainbow.algorithms.proofs.ahof.smc :as smc]))

(def AT [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the certificate"}])
(def IF [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'logic/if-data :statement "eliminator is present"}])
(def MUL [{:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}
          {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present"}])
(def AR [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
         {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}])
(defn- m [e d t] [{:extend e :defs d :thms t}])

(def configs
  [{:id "O11" :name "Shubert-Piyavskii" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Sawtooth Lipschitz lower bound; sample where the lower bound is smallest, keeping the smaller lower-bound value."
    :kind :ahof-o11-shubert :dir "artifacts/ahof/o11-shubert"
    :modules (m sh/extend-environment sh/definition-ids sh/theorem-ids) :baseline-prereqs IF
    :package 'shubert/selected-value
    :claim-boundaries {:exact-rational-only true :min-lower-bound-selection :proved :lipschitz-constant :not-claimed}
    :spec {:module 'shubert :headline 'shubert/sample-value}}
   {:id "D38" :name "Labeled Heuristic Search (LAO*)" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Expand the lowest f-cost node of the explicit AND/OR graph frontier."
    :kind :ahof-d38-lao-star :dir "artifacts/ahof/d38-lao-star"
    :modules (m lao/extend-environment lao/definition-ids lao/theorem-ids) :baseline-prereqs IF
    :package 'lao/selected-value
    :claim-boundaries {:exact-rational-only true :min-f-selection :proved :graph-expansion :not-claimed}
    :spec {:module 'lao :headline 'lao/expand-value}}
   {:id "V17" :name "Tree Search for Falsification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Best-first search over behaviours toward a violation, expanding the lowest cost-to-violation node."
    :kind :ahof-v17-tree-search-fal :dir "artifacts/ahof/v17-tree-search-fal"
    :modules (m tf/extend-environment tf/definition-ids tf/theorem-ids) :baseline-prereqs IF
    :package 'tree-fal/selected-value
    :claim-boundaries {:exact-rational-only true :min-cost-selection :proved :search-strategy :not-claimed}
    :spec {:module 'tree-fal :headline 'tree-fal/frontier-value}}
   {:id "D44" :name "Isotropic Evolutionary Strategies" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Perturb with isotropic Gaussian noise and keep the fitter offspring."
    :kind :ahof-d44-isotropic-es :dir "artifacts/ahof/d44-isotropic-es"
    :modules (m ies/extend-environment ies/definition-ids ies/theorem-ids) :baseline-prereqs IF
    :package 'iso-es/selected-value
    :claim-boundaries {:exact-rational-only true :max-fitness-selection :proved :step-size-adaptation :not-claimed}
    :spec {:module 'iso-es :headline 'iso-es/selected-fitness}}
   {:id "D56" :name "Actor-Critic with MCTS" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Guide tree search by the critic; select the child with the larger UCB-augmented value."
    :kind :ahof-d56-ac-mcts :dir "artifacts/ahof/d56-ac-mcts"
    :modules (m acm/extend-environment acm/definition-ids acm/theorem-ids) :baseline-prereqs IF
    :package 'ac-mcts/selected-value
    :claim-boundaries {:exact-rational-only true :max-value-selection :proved :critic-training :not-claimed}
    :spec {:module 'ac-mcts :headline 'ac-mcts/node-value}}
   {:id "D76" :name "Finite State Controller" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "A POMDP policy as a finite-state machine; at a node it selects the higher-value action."
    :kind :ahof-d76-finite-state-controller :dir "artifacts/ahof/d76-finite-state-controller"
    :modules (m fsc/extend-environment fsc/definition-ids fsc/theorem-ids) :baseline-prereqs IF
    :package 'fsc/selected-value
    :claim-boundaries {:exact-rational-only true :max-action-selection :proved :controller-synthesis :not-claimed}
    :spec {:module 'fsc :headline 'fsc/node-value}}
   {:id "D39" :name "Open-Loop Planning" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Optimize a fixed open-loop action sequence, keeping the plan with the larger total value."
    :kind :ahof-d39-open-loop-planning :dir "artifacts/ahof/d39-open-loop-planning"
    :modules (m olp/extend-environment olp/definition-ids olp/theorem-ids) :baseline-prereqs IF
    :package 'olp/selected-value
    :claim-boundaries {:exact-rational-only true :max-plan-selection :proved :horizon-rollout :not-claimed}
    :spec {:module 'olp :headline 'olp/best-plan-value}}
   {:id "D83" :name "Dec-POMDP Heuristic Search" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Search joint policies with heuristic bounds; converged when the bound gap is within precision."
    :kind :ahof-d83-dec-pomdp-hs :dir "artifacts/ahof/d83-dec-pomdp-hs"
    :modules (m dhs/extend-environment dhs/definition-ids dhs/theorem-ids) :baseline-prereqs AT
    :package 'dec-hs/small-gap-converged
    :claim-boundaries {:exact-rational-only true :bound-gap-convergence :proved :joint-policy-search :not-claimed}
    :spec {:module 'dec-hs :headline 'dec-hs/converged?}}
   {:id "V3" :name "Agent Model Construction" :source-file "catalog/03_validation_algorithms.md"
    :listing "Fit a model of another agent; the model fits when its prediction error is within tolerance."
    :kind :ahof-v3-agent-model :dir "artifacts/ahof/v3-agent-model"
    :modules (m am/extend-environment am/definition-ids am/theorem-ids) :baseline-prereqs AT
    :package 'agent-model/low-error-fits
    :claim-boundaries {:exact-rational-only true :fit-error-decision :proved :model-class :not-claimed}
    :spec {:module 'agent-model :headline 'agent-model/model-fits?}}
   {:id "V10" :name "Disturbance-Based Falsification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Search bounded disturbances to drive a violation; found when robustness drops to or below the margin."
    :kind :ahof-v10-disturbance-falsification :dir "artifacts/ahof/v10-disturbance-falsification"
    :modules (m df/extend-environment df/definition-ids df/theorem-ids) :baseline-prereqs AT
    :package 'dist-fal/low-robustness-violation
    :claim-boundaries {:exact-rational-only true :robustness-violation-decision :proved :disturbance-search :not-claimed}
    :spec {:module 'dist-fal :headline 'dist-fal/violation?}}
   {:id "V23" :name "Gibbs Sampling (Failures)" :source-file "catalog/03_validation_algorithms.md"
    :listing "Reuse Gibbs structure over the failure region; the draw is from the conditional when the uniform sample falls under the conditional mass."
    :kind :ahof-v23-gibbs-failures :dir "artifacts/ahof/v23-gibbs-failures"
    :modules (m gf/extend-environment gf/definition-ids gf/theorem-ids) :baseline-prereqs AT
    :package 'gibbs-fail/draw-under-mass
    :claim-boundaries {:exact-rational-only true :conditional-draw-decision :proved :full-conditional :not-claimed}
    :spec {:module 'gibbs-fail :headline 'gibbs-fail/draws-conditional?}}
   {:id "D1" :name "Bayesian Network Representation" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "The joint distribution factorizes as a product of conditional-probability factors; the joint mass of two factors is their product."
    :kind :ahof-d1-bayes-net :dir "artifacts/ahof/d1-bayes-net"
    :modules (m bn/extend-environment bn/definition-ids bn/theorem-ids) :baseline-prereqs MUL
    :package 'bayes-net/combined
    :claim-boundaries {:exact-rational-only true :factor-product :proved :graph-structure :not-claimed}
    :spec {:module 'bayes-net :headline 'bayes-net/joint-factor}}
   {:id "V25" :name "Probabilistic Programming" :source-file "catalog/03_validation_algorithms.md"
    :listing "An observe/factor statement reweights the trace by the observation likelihood; the score combines factors multiplicatively."
    :kind :ahof-v25-prob-programming :dir "artifacts/ahof/v25-prob-programming"
    :modules (m pp/extend-environment pp/definition-ids pp/theorem-ids) :baseline-prereqs MUL
    :package 'prob-prog/combined
    :claim-boundaries {:exact-rational-only true :trace-score-product :proved :inference-backend :not-claimed}
    :spec {:module 'prob-prog :headline 'prob-prog/score}}
   {:id "V30" :name "Sequential Monte Carlo" :source-file "catalog/03_validation_algorithms.md"
    :listing "Propagate and resample a weighted particle set over time; the filtered estimate is the normalized weighted mean of particles."
    :kind :ahof-v30-smc :dir "artifacts/ahof/v30-smc"
    :modules (m smc/extend-environment smc/definition-ids smc/theorem-ids) :baseline-prereqs AR
    :package 'smc/combined
    :claim-boundaries {:exact-rational-only true :weighted-particle-mean :proved :resampling-scheme :not-claimed}
    :spec {:module 'smc :headline 'smc/estimate}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
