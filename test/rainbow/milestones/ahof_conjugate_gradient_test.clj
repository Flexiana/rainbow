(ns rainbow.milestones.ahof-conjugate-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-conjugate-gradient :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o18-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o18 (first (filter #(= "O18" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o18)))
    (is (= (:evidence/id report)
           (get-in o18 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o18-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/conjugate-direction
                   optimization/conjugate-step
                   optimization/conjugate-iterate
                   optimization/conjugate-direction-unfold
                   optimization/conjugate-step-unfold
                   optimization/conjugate-iterate-zero
                   ahof-o18/first-direction-is-negative-one
                   ahof-o18/first-position-is-three-halves
                   ahof-o18/conjugate-recurrence
                   ahof-o18/conjugate-gradient]]
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

(deftest worked-conjugate-gradient-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [3/2 -1]
           (get-in report [:evaluation :clojure-reference
                           :conjugate-first-step])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :separate-step-size-differs])))
    (is (= :proved (get-in report [:claim-boundaries :remembered-direction])))
    (is (= :computed-observation
           (get-in report [:claim-boundaries :separate-step-size])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :conjugacy-guarantee])))))
