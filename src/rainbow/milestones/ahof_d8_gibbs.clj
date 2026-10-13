(ns rainbow.milestones.ahof-d8-gibbs
  "Content-addressed credit for AHoF D8 Gibbs Sampling via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.gibbs :as m]))

(def config
  {:id "D8" :name "Gibbs Sampling"
   :source-file "catalog/02_decision_making_algorithms.md"
   :listing "Resample each variable in turn from its full conditional given the others; the accept decision selects the drawn value from the conditional."
   :kind :ahof-d8-gibbs
   :dir "artifacts/ahof/d8-gibbs"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'audit/decide-nnrat-at-most
     :statement "the exact-rational order decision is present for the conditional draw"}
    {:target/name 'nnrat/at-most
     :statement "the exact-rational order relation is present for the draw witness"}]
   :package 'gibbs/draw-is-from-conditional
   :claim-boundaries {:exact-rational-only true
                      :conditional-draw-decision :proved
                      :draw-from-conditional :proved
                      :full-conditional-distribution :not-claimed
                      :stationary-distribution-convergence :not-claimed}
   :spec {:draws 'gibbs/draws?
          :conditional-law 'gibbs/draw-is-from-conditional}})

(defn -main [& args] (credit/main config args))
