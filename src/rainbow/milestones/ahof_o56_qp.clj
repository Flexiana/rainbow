(ns rainbow.milestones.ahof-o56-qp
  "Content-addressed credit for AHoF O56 QP Solver via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.qp :as m]))

(def config
  {:id "O56" :name "QP Solver"
   :source-file "catalog/01_optimization_algorithms.md"
   :listing "Encode QP as a KKT system. The quadratic objective (1/2) x' Q x + c' x is evaluated over exact rationals."
   :kind :ahof-o56-qp
   :dir "artifacts/ahof/o56-qp"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'nnrat/add
     :statement "exact-rational addition is present for the quadratic objective"}
    {:target/name 'nnrat/multiply
     :statement "exact-rational multiplication is present for the quadratic term"}]
   :package 'qp/objective-at-zero
   :claim-boundaries {:exact-rational-only true
                      :quadratic-objective :proved
                      :objective-at-zero :proved
                      :kkt-system-solution :not-claimed
                      :active-set-iteration :not-claimed}
   :spec {:objective 'qp/objective :zero-law 'qp/objective-at-zero}})

(defn -main [& args] (credit/main config args))
