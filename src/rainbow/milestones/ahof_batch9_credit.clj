(ns rainbow.milestones.ahof-batch9-credit
  "Ninth batch: four fresh native proofs -- V63 Runtime STL Monitor,
  V61 Ensemble Disagreement, D12 KDE, O37 DIRECT."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.stl-monitor :as stl]
            [rainbow.algorithms.proofs.ahof.ensemble-disagreement :as ens]
            [rainbow.algorithms.proofs.ahof.kde :as kde]
            [rainbow.algorithms.proofs.ahof.direct :as dir]))

(def configs
  [{:id "V63" :name "Runtime STL Monitor"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Online monitoring of a Signal Temporal Logic spec: satisfied while the robustness margin stays at or above the required safety margin."
    :kind :ahof-v63-stl-monitor
    :dir "artifacts/ahof/v63-stl-monitor"
    :modules [{:extend stl/extend-environment :defs stl/definition-ids :thms stl/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the robustness certificate"}]
    :package 'stl-monitor/satisfied-above-margin
    :claim-boundaries {:exact-rational-only true :robustness-margin-monitor :proved :margin-certificate :proved
                       :temporal-operator-semantics :not-claimed :signed-robustness :not-claimed}
    :spec {:module 'stl-monitor :headline 'stl-monitor/satisfied?}}
   {:id "V61" :name "Ensemble Disagreement"
    :source-file "catalog/03_validation_algorithms.md"
    :listing "Quantify predictive uncertainty by ensemble spread and flag an input as uncertain when the disagreement reaches a threshold."
    :kind :ahof-v61-ensemble-disagreement
    :dir "artifacts/ahof/v61-ensemble-disagreement"
    :modules [{:extend ens/extend-environment :defs ens/definition-ids :thms ens/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the disagreement certificate"}]
    :package 'ensemble/high-disagreement-flagged
    :claim-boundaries {:exact-rational-only true :disagreement-threshold-decision :proved :disagreement-certificate :proved
                       :spread-statistic-formula :not-claimed :calibration :not-claimed}
    :spec {:module 'ensemble :headline 'ensemble/flag-uncertain?}}
   {:id "D12" :name "Nonparametric Learning (KDE)"
    :source-file "catalog/02_decision_making_algorithms.md"
    :listing "Kernel density estimation: a data point contributes to the density at a query point exactly when it lies within the bandwidth window."
    :kind :ahof-d12-kde
    :dir "artifacts/ahof/d12-kde"
    :modules [{:extend kde/extend-environment :defs kde/definition-ids :thms kde/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the support certificate"}]
    :package 'kde/within-window-contributes
    :claim-boundaries {:exact-rational-only true :bandwidth-window-decision :proved :support-certificate :proved
                       :kernel-shape :not-claimed :density-normalization :not-claimed}
    :spec {:module 'kde :headline 'kde/in-bandwidth?}}
   {:id "O37" :name "DIRECT (Divided Rectangles)"
    :source-file "catalog/01_optimization_algorithms.md"
    :listing "DIvided RECTangles global optimizer: among rectangles of comparable size the more promising one has the smaller center value; the selection core is the minimum of two center values."
    :kind :ahof-o37-direct
    :dir "artifacts/ahof/o37-direct"
    :modules [{:extend dir/extend-environment :defs dir/definition-ids :thms dir/theorem-ids}]
    :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                       {:target/name 'logic/if-data :statement "eliminator is present for the min"}]
    :package 'direct-opt/selects-lower-center
    :claim-boundaries {:exact-rational-only true :promising-rectangle-min :proved :preference-decision :proved
                       :potentially-optimal-hull :not-claimed :lipschitz-bound :not-claimed}
    :spec {:module 'direct-opt :headline 'direct-opt/more-promising}}])

(defn -main [& args]
  (if (seq args)
    (credit/credit-batch! configs (Integer/parseInt (first args)) (Integer/parseInt (second args)))
    (credit/credit-batch! configs))
  (shutdown-agents))
