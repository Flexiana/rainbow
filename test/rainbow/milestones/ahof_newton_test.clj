(ns rainbow.milestones.ahof-newton-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-newton :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o26-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o26 (first (filter #(= "O26" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o26)))
    (is (= (:evidence/id report)
           (get-in o26 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o26-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[nnrat/reciprocal
                   nnrat/divide
                   nnrat/divide-self-positive
                   optimization/newton-rate
                   optimization/newton-rate-unfold
                   ahof-o26/step-size
                   ahof-o26/reaches-minimum-in-one-step
                   ahof-o26/newton-recurrence
                   ahof-o26/newton]]
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

(deftest worked-newton-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :newton-rate])))
    (is (= 0 (get-in report [:evaluation :clojure-reference :first-step])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :reaches-minimum-in-one-step])))
    (is (= :proved
           (get-in report [:claim-boundaries :quadratic-one-step-convergence])))
    (is (= :proved
           (get-in report [:claim-boundaries :rational-division-used])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :general-convergence])))))
