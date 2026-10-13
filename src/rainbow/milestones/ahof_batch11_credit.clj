(ns rainbow.milestones.ahof-batch11-credit
  "Eleventh batch: five fresh native proofs -- D73 HSVI, V58 Failure Mode
  Characterization, D71 Alpha Vector, D59 Bayesian Model Estimation,
  D52 Clamped Surrogate Objective."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.hsvi :as hsvi]
            [rainbow.algorithms.proofs.ahof.failure-mode :as fm]
            [rainbow.algorithms.proofs.ahof.alpha-vector :as av]
            [rainbow.algorithms.proofs.ahof.bayesian-model-estimation :as me]
            [rainbow.algorithms.proofs.ahof.clamped-surrogate :as clip]))

(def configs
  [{:id "D73" :name "HSVI"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Heuristic Search Value Iteration for POMDPs: search belief points to tighten upper/lower value bounds; converged when the bound gap is within precision."
    :kind :ahof-d73-hsvi
    :dir "artifacts/ahof/d73-hsvi"
    :modules [{:extend hsvi/extend-environment :defs hsvi/definition-ids :thms hsvi/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the gap certificate"}]
    :package 'hsvi/small-gap-converged
    :claim-boundaries {:exact-rational-only true :bound-gap-convergence :proved :gap-certificate :proved
                       :belief-point-selection :not-claimed :bound-backup-formula :not-claimed}
    :spec {:module 'hsvi :headline 'hsvi/converged?}}
   {:id "V58" :name "Failure Mode Characterization"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Cluster observed failures into modes; assign a new failure to a mode when its distance to the centroid is within the mode radius."
    :kind :ahof-v58-failure-mode
    :dir "artifacts/ahof/v58-failure-mode"
    :modules [{:extend fm/extend-environment :defs fm/definition-ids :thms fm/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the membership certificate"}]
    :package 'failure-mode/within-radius-in-mode
    :claim-boundaries {:exact-rational-only true :radius-membership-decision :proved :membership-certificate :proved
                       :centroid-computation :not-claimed :cluster-count-selection :not-claimed}
    :spec {:module 'failure-mode :headline 'failure-mode/in-mode?}}
   {:id "D71" :name "Alpha Vector (Exact POMDP)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "The optimal POMDP value at a belief is the maximum over the alpha-vector set of the inner products; with two vectors it picks the larger value."
    :kind :ahof-d71-alpha-vector
    :dir "artifacts/ahof/d71-alpha-vector"
    :modules [{:extend av/extend-environment :defs av/definition-ids :thms av/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the value max"}]
    :package 'alpha-vector/value-is-maximum
    :claim-boundaries {:exact-rational-only true :value-maximum :proved :dominance-decision :proved
                       :inner-product-computation :not-claimed :vector-pruning :not-claimed}
    :spec {:module 'alpha-vector :headline 'alpha-vector/best-value}}
   {:id "D59" :name "Bayesian Model Estimation"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Score candidate models by posterior probability, proportional to data likelihood under the model times the model prior."
    :kind :ahof-d59-model-estimation
    :dir "artifacts/ahof/d59-model-estimation"
    :modules [{:extend me/extend-environment :defs me/definition-ids :thms me/theorem-ids}]
    :baseline-prereqs [{:target/name 'nnrat/multiply :statement "exact-rational multiplication is present"}
                       {:target/name 'nnrat/equivalent :statement "exact-rational equivalence is present for the scores"}]
    :package 'model-est/model-estimation
    :claim-boundaries {:exact-rational-only true :posterior-score-product :proved :posterior-concentration :proved
                       :normalization-constant :not-claimed :marginal-likelihood :not-claimed}
    :spec {:module 'model-est :headline 'model-est/posterior-score}}
   {:id "D52" :name "Clamped Surrogate Objective"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "PPO clips the probability ratio into a trust region [1-eps, 1+eps] before forming the surrogate objective: clamp r lo hi = min (max r lo) hi."
    :kind :ahof-d52-clamped-surrogate
    :dir "artifacts/ahof/d52-clamped-surrogate"
    :modules [{:extend clip/extend-environment :defs clip/definition-ids :thms clip/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the nested min/max"}]
    :package 'clip/inside-region-unchanged
    :claim-boundaries {:exact-rational-only true :ratio-clamp :proved :three-regimes :proved
                       :advantage-weighting :not-claimed :gradient-estimator :not-claimed}
    :spec {:module 'clip :headline 'clip/clamp}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
