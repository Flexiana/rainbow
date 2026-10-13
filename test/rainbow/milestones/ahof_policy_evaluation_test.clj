(ns rainbow.milestones.ahof-policy-evaluation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-policy-evaluation :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d20-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d20 (first (filter #(= "D20" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d20)))
    (is (= (:evidence/id report)
           (get-in d20 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [2 2]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d20-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[bellman/nnrat-value-iterate-successor
                   bellman/nnrat-value-iterate-congruent
                   bellman/nnrat-value-iterate-model-transfer
                   bellman/nnrat-value-iterate-initial-transfer
                   ahof-d20/finite-horizon-recurrence
                   ahof-d20/normalized-transition-rows
                   ahof-d20/one-step-value
                   ahof-d20/two-step-value
                   ahof-d20/policy-evaluation]]
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

(deftest bounded-claim-does-not-imply-unproved-convergence
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (every? :matches? (get-in report [:evaluation :outputs])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :infinite-limit-convergence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :unique-fixed-point])))))
