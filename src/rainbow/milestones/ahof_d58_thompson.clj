(ns rainbow.milestones.ahof-d58-thompson
  "Content-addressed credit for AHoF D58 Thompson Sampling via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.thompson :as m]))

(def config
  {:id "D58" :name "Thompson Sampling"
   :source-file "catalog/02_decision_making_algorithms.md"
   :listing "(make-bandit-strategy :thompson). Draw a sample from each arm's posterior and pull the arm with the largest sampled value."
   :kind :ahof-d58-thompson
   :dir "artifacts/ahof/d58-thompson"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'audit/decide-nnrat-at-most
     :statement "the exact-rational order decision is present for the argmax selection"}
    {:target/name 'nnrat/at-most
     :statement "the exact-rational order relation is present for the domination witness"}]
   :package 'thompson/selects-largest-sample
   :claim-boundaries {:exact-rational-only true
                      :largest-sample-selection :proved
                      :selected-dominates-others :proved
                      :posterior-sampling-distribution :not-claimed
                      :regret-bound :not-claimed}
   :spec {:select 'thompson/select
          :selection-law 'thompson/selects-largest-sample}})

(defn -main [& args] (credit/main config args))
