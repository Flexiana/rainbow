(ns rainbow.milestones.ahof-value-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-value-iteration :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d22-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d22 (first (filter #(= "D22" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d22)))
    (is (= (:evidence/id report)
           (get-in d22 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 7] :after [7 7]}
           (get-in report [:results :held-out])))
    (is (= {:after [2 2]} (get-in report [:results :transfer])))
    (is (= 13 (get-in report [:results :newly-solved-native-results])))
    (is (= 1237 (get-in report [:checkpoint :exact-mathlib-mappings])))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d22-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[bellman/nnrat-action-backup-unfold
                   value/nnrat-greedy-action-is-admissible
                   value/nnrat-optimality-step-dominates
                   value/nnrat-optimality-step-unfold
                   value/nnrat-iterate-zero
                   value/nnrat-iterate-successor
                   value/nnrat-optimality-state-transfer
                   ahof-d22/action-backup-correspondence
                   ahof-d22/normalized-transition-rows
                   ahof-d22/finite-horizon-recurrence
                   ahof-d22/greedy-actions
                   ahof-d22/two-step-value
                   ahof-d22/value-iteration]]
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

(deftest worked-value-iteration-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (every? :matches?
                (get-in report [:evaluation :rainbow :values])))
    (is (= [:zero :zero]
           (mapv :selected-action
                 (get-in report [:evaluation :rainbow :greedy-actions]))))
    (is (= {0 0, 1 0}
           (get-in report [:evaluation :clojure-reference :values])))
    (is (= :proved
           (get-in report
                   [:claim-boundaries
                    :bounded-bellman-optimality-iteration])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report
                   [:claim-boundaries :infinite-limit-convergence])))))
