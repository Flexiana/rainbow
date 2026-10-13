(ns rainbow.milestones.ahof-v60-conformal
  "Content-addressed credit for AHoF V60 Conformal Prediction via the generic runner."
  (:require [rainbow.milestones.ahof-module-credit :as credit]
            [rainbow.algorithms.proofs.ahof.conformal :as m]))

(def config
  {:id "V60" :name "Conformal Prediction"
   :source-file "catalog/03_validation_algorithms.md"
   :listing "(make-conformal-predictor calibration alpha). A label is in the prediction set when its nonconformity score is at most the (1-alpha)-quantile threshold."
   :kind :ahof-v60-conformal
   :dir "artifacts/ahof/v60-conformal"
   :modules [{:extend m/extend-environment :defs m/definition-ids :thms m/theorem-ids}]
   :baseline-prereqs
   [{:target/name 'audit/decide-nnrat-at-most
     :statement "the exact-rational order decision is present for the inclusion test"}
    {:target/name 'nnrat/at-most
     :statement "the exact-rational order relation is present for the coverage guarantee"}]
   :package 'conformal/included-within-threshold
   :claim-boundaries {:exact-rational-only true
                      :inclusion-threshold-test :proved
                      :included-score-at-most-threshold :proved
                      :empirical-quantile-computation :not-claimed
                      :finite-sample-coverage-probability :not-claimed}
   :spec {:inclusion 'conformal/in-prediction-set?
          :coverage-witness 'conformal/included-within-threshold}})

(defn -main [& args] (credit/main config args))
