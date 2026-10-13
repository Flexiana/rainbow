(ns rainbow.milestones.ahof-v57-counterfactual
  "Content-addressed credit for AHoF V57 Counterfactual Explanation via the generic
  runner -- the final catalog row."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.counterfactual-cf :as cf]))

(def config
  {:id "V57" :name "Counterfactual Explanation"
   :source-file "catalog/03_validation_algorithms.md"
   :listing "Explain a decision by the smallest input change that flips the prediction; a candidate counterfactual is accepted when its change cost is within the action budget."
   :kind :ahof-v57-counterfactual
   :dir "artifacts/ahof/v57-counterfactual"
   :modules [{:extend cf/extend-environment :defs cf/definition-ids :thms cf/theorem-ids}]
   :baseline-prereqs [{:target/name 'audit/decide-nnrat-at-most :statement "exact-rational order decision is present"}
                      {:target/name 'nnrat/at-most :statement "exact-rational order relation is present for the proximity certificate"}]
   :package 'cf/within-budget-valid
   :claim-boundaries {:exact-rational-only true :cost-budget-decision :proved :proximity-certificate :proved
                      :feature-search :not-claimed :plausibility-constraint :not-claimed}
   :spec {:module 'cf :headline 'cf/valid-counterfactual?}})

(defn -main [& args] (credit/main config args))
