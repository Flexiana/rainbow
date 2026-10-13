(ns rainbow.milestones.ahof-nesterov-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-nesterov :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o20-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o20 (first (filter #(= "O20" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o20)))
    (is (= (:evidence/id report)
           (get-in o20 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o20-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/nesterov-lookahead
                   optimization/nesterov-velocity
                   optimization/nesterov-step
                   optimization/nesterov-iterate
                   optimization/nesterov-step-unfold
                   optimization/nesterov-iterate-zero
                   ahof-o20/first-velocity-is-negative-one
                   ahof-o20/first-position-is-zero
                   ahof-o20/nesterov-recurrence
                   ahof-o20/nesterov]]
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

(deftest worked-nesterov-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [0 -1]
           (get-in report [:evaluation :clojure-reference :nesterov-first-step])))
    (is (= [1 0]
           (get-in report [:evaluation :clojure-reference :momentum-first-step])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :look-ahead-changes-trajectory])))
    (is (= :proved (get-in report [:claim-boundaries :look-ahead-gradient])))
    (is (= :computed-observation
           (get-in report [:claim-boundaries :distinct-from-momentum])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :acceleration-theorem])))))
