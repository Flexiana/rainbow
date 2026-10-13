(ns rainbow.milestones.ahof-gradient-descent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-gradient-descent :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o17-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o17 (first (filter #(= "O17" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o17)))
    (is (= (:evidence/id report)
           (get-in o17 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 8 (get-in report [:results :newly-solved-native-results])))
    ;; This milestone honestly records the kernel reduction-budget increase.
    (is (= :kernel-reduction-budget-raised (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o17-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/signed-descent-step
                   optimization/signed-descent-iterate
                   optimization/signed-descent-step-unfold
                   optimization/signed-descent-iterate-zero
                   optimization/signed-descent-iterate-successor
                   ahof-o17/trajectory-values
                   ahof-o17/descent-recurrence
                   ahof-o17/gradient-descent]]
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

(deftest worked-descent-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [1 1/2 0 -1/2]
           (get-in report [:evaluation :clojure-reference :trajectory])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :reaches-negative])))
    (is (= :proved (get-in report [:claim-boundaries :reaches-negative-values])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :convergence-to-minimum])))))
