(ns rainbow.milestones.ahof-o48-penalty
  "Content-addressed credit for AHoF O48 Penalty Method, reusing the native proof in
  rainbow.algorithms.proofs.ahof.penalty via the generic module-credit runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.penalty :as penalty]))

(def config
  {:id "O48"
   :name "Penalty Method"
   :source-file "catalog/01_optimization_algorithms.md"
   :listing "(comp unconstrained-solver (add-penalty constraint)). Constrained problem becomes a sequence of unconstrained ones."
   :kind :ahof-o48-penalty
   :dir "artifacts/ahof/o48-penalty"
   :modules [{:extend penalty/extend-environment
              :defs penalty/definition-ids
              :thms penalty/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'nnrat/add
     :statement "exact-rational addition is present for the penalized objective"}
    {:target/name 'nnrat/multiply
     :statement "exact-rational multiplication is present for the penalty term"}]
   :package 'penalty/feasible-equals-objective
   :representation {:penalized :objective-plus-coefficient-times-violation
                    :feasible-point :penalty-vanishes}
   :claim-boundaries {:exact-rational-only true
                      :penalized-objective-combination :proved
                      :feasible-equals-objective :proved
                      :outer-iteration-schedule :not-claimed
                      :convergence-to-feasibility :not-claimed}
   :statements
   {'penalty/penalized "the penalized objective is f + mu * violation"
    'penalty/penalized-example "a worked penalized objective value is computed"
    'penalty/feasible-equals-objective
    "at a feasible point (zero violation) the penalized objective equals the original"}
   :spec {:penalized 'penalty/penalized
          :feasible-law 'penalty/feasible-equals-objective}})

(defn -main [& args] (credit/main config args))
