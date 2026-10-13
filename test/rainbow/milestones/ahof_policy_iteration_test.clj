(ns rainbow.milestones.ahof-policy-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-policy-iteration :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d21-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d21 (first (filter #(= "D21" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d21)))
    (is (= (:evidence/id report)
           (get-in d21 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [2 2]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= 1237 (get-in report [:checkpoint :exact-mathlib-mappings])))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d21-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[policy/nnrat-improve-is-admissible
                   policy/nnrat-improve-dominates
                   policy/nnrat-iteration-step-unfold
                   policy/nnrat-improvement-model-transfer
                   policy/nnrat-improvement-state-transfer
                   ahof-d21/current-policy-admissible
                   ahof-d21/evaluation-phase
                   ahof-d21/improvement-phase
                   ahof-d21/policy-iteration-step]]
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

(deftest worked-step-is-computed-without-overclaiming-convergence
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [:one :one]
           (mapv :selected-action (get-in report [:evaluation :outputs]))))
    (is (every? :matches? (get-in report [:evaluation :outputs])))
    (is (= :proved
           (get-in report
                   [:claim-boundaries :one-evaluate-then-improve-step])))
    (is (= :not-claimed
           (get-in report
                   [:claim-boundaries :termination-at-optimal-policy])))
    (is (= :not-claimed
           (get-in report
                   [:claim-boundaries :infinite-limit-convergence])))))
