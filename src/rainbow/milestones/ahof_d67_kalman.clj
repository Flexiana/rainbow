(ns rainbow.milestones.ahof-d67-kalman
  "Content-addressed credit for AHoF D67 Kalman Filter via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.kalman :as m]))

(def config
  {:id "D67" :name "Kalman Filter"
   :source-file "catalog/02_decision_making_algorithms.md"
   :listing "(make-kalman-filter A B C Q R). Recursive linear-Gaussian state estimator: gain blends prediction and measurement; posterior updates the estimate."
   :kind :ahof-d67-kalman
   :dir "artifacts/ahof/d67-kalman"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'nnrat/add
     :statement "exact-rational addition is present for the posterior update"}
    {:target/name 'nnrat/multiply
     :statement "exact-rational multiplication is present for the gain blend"}]
   :package 'kalman/balanced-posterior
   :claim-boundaries {:exact-rational-only true
                      :gain-blend :proved
                      :posterior-update :proved
                      :covariance-propagation :not-claimed
                      :multivariate-matrix-form :not-claimed}
   :spec {:gain 'kalman/gain :posterior 'kalman/posterior}})

(defn -main [& args] (credit/main config args))
