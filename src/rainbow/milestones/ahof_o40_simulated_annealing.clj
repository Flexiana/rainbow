(ns rainbow.milestones.ahof-o40-simulated-annealing
  "Content-addressed credit for AHoF O40 Simulated Annealing via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.simulated-annealing :as m]))

(def config
  {:id "O40" :name "Simulated Annealing"
   :source-file "catalog/01_optimization_algorithms.md"
   :listing "Global optimization metaheuristic: accept a worse (uphill) candidate with the Metropolis probability exp(-delta/T) as the temperature cools."
   :kind :ahof-o40-simulated-annealing
   :dir "artifacts/ahof/o40-simulated-annealing"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'audit/decide-nnrat-at-most
     :statement "the exact-rational order decision is present for the acceptance test"}
    {:target/name 'nnrat/at-most
     :statement "the exact-rational order relation is present for the acceptance certificate"}]
   :package 'simulated-annealing/accepts-worse-move
   :claim-boundaries {:exact-rational-only true
                      :metropolis-acceptance-decision :proved
                      :accepts-within-band :proved
                      :rejects-above-band :proved
                      :cooling-schedule :not-claimed
                      :convergence-in-distribution :not-claimed}
   :spec {:accepts 'simulated-annealing/accepts-uphill?
          :acceptance-law 'simulated-annealing/accepts-worse-move}})

(defn -main [& args] (credit/main config args))
