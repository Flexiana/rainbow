(ns rainbow.milestones.ahof-batch18-credit
  "Eighteenth batch: fourteen fresh native proofs -- O14 O15 O75 D6 D41 D82
  V1 V7 V14 V15 V48 V28 V55 D70."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.backtracking :as bt]
            [rainbow.algorithms.proofs.ahof.prob-robust :as prb]
            [rainbow.algorithms.proofs.ahof.rejection :as rj]
            [rainbow.algorithms.proofs.ahof.ltl-model-checking :as ltl]
            [rainbow.algorithms.proofs.ahof.cmaes-falsification :as cf]
            [rainbow.algorithms.proofs.ahof.ce-falsification :as cef]
            [rainbow.algorithms.proofs.ahof.bfs-reachability :as bfs]
            [rainbow.algorithms.proofs.ahof.ga-policy :as ga]
            [rainbow.algorithms.proofs.ahof.dec-pomdp-dp :as dp]
            [rainbow.algorithms.proofs.ahof.mle-system :as mle]
            [rainbow.algorithms.proofs.ahof.strong-wolfe :as sw]
            [rainbow.algorithms.proofs.ahof.adaptive-is :as ais]
            [rainbow.algorithms.proofs.ahof.shap :as shap]
            [rainbow.algorithms.proofs.ahof.particle-filter-pf :as pf]))

(def AT [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the certificate"}])
(def IF [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
         {:target/name 'logic/if-data :statement "eliminator is present"}])
(def AR [{:target/name 'nnrat/add :statement "exact-rational addition is present"}
         {:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}])
(def DIV [{:target/name 'nnrat/divide :statement "exact-rational division is present"}
          {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present"}])
(defn- m [e d t] [{:extend e :defs d :thms t}])
(defn- cb [pairs] (into {:exact-rational-only true} (map (fn [[k v]] [k v])) pairs))

(def configs
  [{:id "O14" :name "Backtracking Line Search" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Shrink the step until the Armijo sufficient-decrease condition holds."
    :kind :ahof-o14-backtracking :dir "artifacts/ahof/o14-backtracking"
    :modules (m bt/extend-environment bt/definition-ids bt/theorem-ids) :baseline-prereqs AT
    :package 'backtrack/accepts-sufficient-decrease
    :claim-boundaries (cb {:armijo-decision :proved :step-schedule :not-claimed})
    :spec {:module 'backtrack :headline 'backtrack/sufficient-decrease?}}
   {:id "O75" :name "Probabilistic Robust Opt" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Satisfy constraints with high probability; chance-feasible when the violation probability is within alpha."
    :kind :ahof-o75-prob-robust :dir "artifacts/ahof/o75-prob-robust"
    :modules (m prb/extend-environment prb/definition-ids prb/theorem-ids) :baseline-prereqs AT
    :package 'prob-robust/low-risk-feasible
    :claim-boundaries (cb {:chance-constraint-decision :proved :scenario-sampling :not-claimed})
    :spec {:module 'prob-robust :headline 'prob-robust/chance-feasible?}}
   {:id "D6" :name "Rejection Sampling" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Accept a proposal when the uniform draw falls under the acceptance ratio f/(Mg)."
    :kind :ahof-d6-rejection :dir "artifacts/ahof/d6-rejection"
    :modules (m rj/extend-environment rj/definition-ids rj/theorem-ids) :baseline-prereqs AT
    :package 'rejection/draw-under-ratio-accepts
    :claim-boundaries (cb {:acceptance-decision :proved :envelope-constant :not-claimed})
    :spec {:module 'rejection :headline 'rejection/accepts?}}
   {:id "V7" :name "LTL Model Checking" :source-file "catalog/03_validation_algorithms.md"
    :listing "Check an LTL specification; quantitatively satisfied when trace robustness meets the margin."
    :kind :ahof-v7-ltl :dir "artifacts/ahof/v7-ltl"
    :modules (m ltl/extend-environment ltl/definition-ids ltl/theorem-ids) :baseline-prereqs AT
    :package 'ltl/robust-trace-satisfies
    :claim-boundaries (cb {:robustness-satisfaction-decision :proved :automaton-product :not-claimed})
    :spec {:module 'ltl :headline 'ltl/satisfied?}}
   {:id "V14" :name "CMA-ES for Falsification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Adapt a Gaussian search toward the failure region using elite (lowest-cost) samples."
    :kind :ahof-v14-cmaes-falsification :dir "artifacts/ahof/v14-cmaes-falsification"
    :modules (m cf/extend-environment cf/definition-ids cf/theorem-ids) :baseline-prereqs AT
    :package 'cmaes-fal/low-cost-elite
    :claim-boundaries (cb {:elite-decision :proved :covariance-adaptation :not-claimed})
    :spec {:module 'cmaes-fal :headline 'cmaes-fal/elite?}}
   {:id "V15" :name "Cross-Entropy for Falsification" :source-file "catalog/03_validation_algorithms.md"
    :listing "Fit the sampling distribution to the failure region by keeping elite low-cost samples."
    :kind :ahof-v15-ce-falsification :dir "artifacts/ahof/v15-ce-falsification"
    :modules (m cef/extend-environment cef/definition-ids cef/theorem-ids) :baseline-prereqs AT
    :package 'ce-fal/low-cost-elite
    :claim-boundaries (cb {:elite-decision :proved :distribution-fitting :not-claimed})
    :spec {:module 'ce-fal :headline 'ce-fal/elite?}}
   {:id "V48" :name "BFS/DFS Graph Reachability" :source-file "catalog/03_validation_algorithms.md"
    :listing "Explore the state graph to decide target reachability; within the frontier when distance is within the radius."
    :kind :ahof-v48-bfs-reachability :dir "artifacts/ahof/v48-bfs-reachability"
    :modules (m bfs/extend-environment bfs/definition-ids bfs/theorem-ids) :baseline-prereqs AT
    :package 'bfs-reach/within-frontier-reachable
    :claim-boundaries (cb {:frontier-membership-decision :proved :graph-traversal :not-claimed})
    :spec {:module 'bfs-reach :headline 'bfs-reach/reachable?}}
   {:id "D41" :name "GA for Policy Search" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Evolve policies under fitness selection, keeping the fitter individual."
    :kind :ahof-d41-ga-policy :dir "artifacts/ahof/d41-ga-policy"
    :modules (m ga/extend-environment ga/definition-ids ga/theorem-ids) :baseline-prereqs IF
    :package 'ga-policy/value-is-maximum
    :claim-boundaries (cb {:fitness-max-selection :proved :crossover-mutation :not-claimed})
    :spec {:module 'ga-policy :headline 'ga-policy/best-fitness}}
   {:id "D82" :name "Dec-POMDP (Dynamic Prog)" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Back up joint-policy values, keeping the larger candidate joint-policy value."
    :kind :ahof-d82-dec-pomdp-dp :dir "artifacts/ahof/d82-dec-pomdp-dp"
    :modules (m dp/extend-environment dp/definition-ids dp/theorem-ids) :baseline-prereqs IF
    :package 'dec-pomdp/value-is-maximum
    :claim-boundaries (cb {:joint-value-max :proved :policy-pruning :not-claimed})
    :spec {:module 'dec-pomdp :headline 'dec-pomdp/backup-value}}
   {:id "V1" :name "MLE for System Models" :source-file "catalog/03_validation_algorithms.md"
    :listing "Fit a system model by maximum likelihood, keeping the model with the larger data likelihood."
    :kind :ahof-v1-mle-system :dir "artifacts/ahof/v1-mle-system"
    :modules (m mle/extend-environment mle/definition-ids mle/theorem-ids) :baseline-prereqs IF
    :package 'mle/value-is-maximum
    :claim-boundaries (cb {:likelihood-max-selection :proved :optimizer :not-claimed})
    :spec {:module 'mle :headline 'mle/best-likelihood}}
   {:id "O15" :name "Strong Wolfe Line Search" :source-file "catalog/01_optimization_algorithms.md"
    :listing "Accept a step only when both the Armijo sufficient-decrease and the curvature condition hold."
    :kind :ahof-o15-strong-wolfe :dir "artifacts/ahof/o15-strong-wolfe"
    :modules (m sw/extend-environment sw/definition-ids sw/theorem-ids) :baseline-prereqs IF
    :package 'wolfe/both-conditions-accept
    :claim-boundaries (cb {:two-condition-conjunction :proved :zoom-phase :not-claimed})
    :spec {:module 'wolfe :headline 'wolfe/wolfe-ok?}}
   {:id "V28" :name "Adaptive Importance Sampling" :source-file "catalog/03_validation_algorithms.md"
    :listing "Iteratively refine the proposal and reweight samples by the target/proposal density ratio."
    :kind :ahof-v28-adaptive-is :dir "artifacts/ahof/v28-adaptive-is"
    :modules (m ais/extend-environment ais/definition-ids ais/theorem-ids) :baseline-prereqs DIV
    :package 'adaptive-is/unequal-is-two
    :claim-boundaries (cb {:importance-ratio :proved :proposal-adaptation :not-claimed})
    :spec {:module 'adaptive-is :headline 'adaptive-is/reweight}}
   {:id "V55" :name "SHAP Values" :source-file "catalog/03_validation_algorithms.md"
    :listing "Attribute a prediction to features as a Shapley-weighted sum of feature contributions."
    :kind :ahof-v55-shap :dir "artifacts/ahof/v55-shap"
    :modules (m shap/extend-environment shap/definition-ids shap/theorem-ids) :baseline-prereqs AR
    :package 'shap/combined
    :claim-boundaries (cb {:weighted-attribution :proved :shapley-weights :not-claimed})
    :spec {:module 'shap :headline 'shap/attribution}}
   {:id "D70" :name "Particle Filter" :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Approximate the posterior by a weighted particle set; the estimate is the weighted particle mean."
    :kind :ahof-d70-particle-filter :dir "artifacts/ahof/d70-particle-filter"
    :modules (m pf/extend-environment pf/definition-ids pf/theorem-ids) :baseline-prereqs AR
    :package 'pfilter/combined
    :claim-boundaries (cb {:weighted-particle-mean :proved :resampling :not-claimed})
    :spec {:module 'pfilter :headline 'pfilter/estimate}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
