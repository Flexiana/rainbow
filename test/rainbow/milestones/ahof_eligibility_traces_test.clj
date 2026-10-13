(ns rainbow.milestones.ahof-eligibility-traces-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-eligibility-traces :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d63-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d63 (first (filter #(= "D63" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d63)))
    (is (= (:evidence/id report)
           (get-in d63 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d63-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[learning/eligibility-trace-update
                   learning/trace-weighted-update
                   learning/eligibility-trace-update-unfold
                   learning/trace-weighted-update-unfold
                   ahof-d63/trace-is-three-halves
                   ahof-d63/value-is-one-half
                   ahof-d63/eligibility-traces]]
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

(deftest worked-eligibility-traces-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3/2 (get-in report [:evaluation :clojure-reference :updated-trace])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :updated-value])))
    (is (= :proved (get-in report [:claim-boundaries :decaying-eligibility-trace])))
    (is (= :proved
           (get-in report [:claim-boundaries :backward-credit-assignment])))
    (is (= :not-claimed (get-in report [:claim-boundaries :convergence])))))
