(ns rainbow.milestones.ahof-bayesian-learning-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-bayesian-learning :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d11-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d11 (first (filter #(= "D11" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d11)))
    (is (= (:evidence/id report)
           (get-in d11 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d11-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[estimation/bayesian-update
                   estimation/bayesian-posterior
                   estimation/bayesian-update-unfold
                   estimation/bayesian-posterior-unfold
                   ahof-d11/first-update-is-three-quarters
                   ahof-d11/posterior-is-one
                   ahof-d11/bayesian-learning]]
      (let [id (environment/resolve-id checked-environment name)
            declaration (environment/declaration checked-environment id)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (= :checked
               (:status
                (kernel/check checked-environment
                              (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))
            (str name))))))

(deftest worked-bayesian-learning-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3/4 (get-in report [:evaluation :clojure-reference :first-update])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :posterior])))
    (is (= [3/2 4/3]
           (get-in report [:evaluation :clojure-reference :likelihoods])))
    (is (= :proved
           (get-in report [:claim-boundaries :sequential-likelihood-update])))
    (is (= :proved (get-in report [:claim-boundaries :posterior-as-product])))
    (is (= :not-claimed (get-in report [:claim-boundaries :normalization])))))
