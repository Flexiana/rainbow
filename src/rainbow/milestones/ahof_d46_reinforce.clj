(ns rainbow.milestones.ahof-d46-reinforce
  "Content-addressed credit for AHoF D46 REINFORCE (Likelihood Ratio) via the generic
  runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.reinforce :as m]))

(def config
  {:id "D46" :name "REINFORCE (Likelihood Ratio)"
   :source-file "catalog/02_decision_making_algorithms.md"
   :listing "(mean (map (fn [tau] (* (grad-log-prob tau) (return tau))) trajectories)). The policy-gradient estimate weights each score by its return."
   :kind :ahof-d46-reinforce
   :dir "artifacts/ahof/d46-reinforce"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'nnrat/add
     :statement "exact-rational addition is present for the estimate aggregation"}
    {:target/name 'nnrat/multiply
     :statement "exact-rational multiplication is present for the score-times-return term"}]
   :package 'reinforce/estimate-example
   :claim-boundaries {:exact-rational-only true
                      :score-times-return-term :proved
                      :zero-return-ignored :proved
                      :trajectory-averaging :not-claimed
                      :unbiasedness-proof :not-claimed}
   :spec {:estimate 'reinforce/estimate
          :zero-return-law 'reinforce/zero-return-ignored}})

(defn -main [& args] (credit/main config args))
